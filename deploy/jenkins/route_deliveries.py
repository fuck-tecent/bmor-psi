"""Resolve pending signed deliveries and persist their CI tasks."""

import argparse
import logging
import sqlite3
from contextlib import closing

from event_jobs import enqueue_delivery, initialize, pending_deliveries
from event_routes import route
from github_app import GitHubApp, RateLimited
from github_revision import StaleDelivery, changed_paths, pull_request


def process(db, app, *, grh_enabled=True):
    initialize(db)
    count = 0
    for delivery, event, body in pending_deliveries(db):
        try:
            paths = ()
            head = None
            if route(event, body, None, grh_enabled=grh_enabled):
                if event == "issue_comment":
                    pr = pull_request(app, body["issue"]["number"])
                    if pr["state"] != "open" or pr["user"]["login"] != body["comment"]["user"]["login"]:
                        raise StaleDelivery("Comment PR is no longer eligible")
                    head = pr["head"]["sha"]
                elif event != "push" or body["ref"] == "refs/heads/main":
                    paths = changed_paths(app, event, body)
            count += enqueue_delivery(db, delivery, event, body, paths, comment_head=head,
                                      grh_enabled=grh_enabled)
        except StaleDelivery:
            with db:
                db.execute("INSERT OR IGNORE INTO routed_deliveries VALUES (?)", (delivery,))
        except (KeyError, TypeError, ValueError) as error:
            # A malformed payload cannot be recovered by retrying it ahead of later deliveries.
            logging.warning("Could not route GitHub delivery %s (%s): %s", delivery, event, error)
            with db:
                db.execute("INSERT OR IGNORE INTO routed_deliveries VALUES (?)", (delivery,))
    return count


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("database")
    parser.add_argument("private_key")
    args = parser.parse_args()
    with closing(sqlite3.connect(args.database, timeout=15)) as db:
        try:
            print(process(db, GitHubApp(args.private_key)))
        except RateLimited as error:
            parser.exit(75, f"{error}\n")


if __name__ == "__main__":
    main()
