"""Short-lived, site-wide counts for the public presence widget."""

import sqlite3
import time
from collections import OrderedDict
from threading import Lock


class SitePresence:
    window = 90
    capacity = 32768

    def __init__(self, desks):
        self.desks = tuple(desks)
        self.visitors = OrderedDict()
        self.lock = Lock()
        self.agent_lock = Lock()
        self.agent_count = None
        self.refresh_at = 0

    def visitor_count(self, visitor=None):
        with self.lock:
            now = time.monotonic()
            while self.visitors and next(iter(self.visitors.values())) <= now - self.window:
                self.visitors.popitem(last=False)
            if visitor is not None:
                self.visitors[visitor] = now
                self.visitors.move_to_end(visitor)
                if len(self.visitors) > self.capacity:
                    self.visitors.popitem(last=False)
            return len(self.visitors)

    def snapshot(self, visitor=None):
        visitors = self.visitor_count(visitor)

        # One small read per desk per ten seconds, shared by all visitors.
        with self.agent_lock:
            if time.monotonic() >= self.refresh_at:
                wall_time = int(time.time())
                count = 0
                try:
                    for desk in self.desks:
                        with desk.transaction() as conn:
                            count += conn.execute("""
                                SELECT COUNT(*) FROM goldbach_leases
                                WHERE submitted_at IS NULL AND released_at IS NULL
                                  AND finished_at IS NULL AND expires_at > ?
                            """, (wall_time,)).fetchone()[0]
                    self.agent_count = count
                except sqlite3.Error:
                    self.agent_count = None
                self.refresh_at = time.monotonic() + 10
            return {"visitors": visitors, "agents": self.agent_count, "window_seconds": self.window}
