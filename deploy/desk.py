import hashlib
import hmac
import ipaddress
import re
import secrets
import sqlite3
import time
from collections import Counter
from contextlib import closing, contextmanager

LEASE_SECONDS = 45 * 60
MAX_RESEARCH_SECONDS = 6 * 60 * 60
SUBMISSION_SECONDS = 12 * 60 * 60
CHECK_SECONDS = 3 * 60 * 60
NETWORK_ACTIVE_LIMIT = 3
NETWORK_HOURLY_LIMIT = 12
FLEET_ACTIVE_LIMIT = 128
QUEUE_BATCH = 16
QUEUE_RETRY_SECONDS = 15 * 60
HANDLE = re.compile(r"[a-z0-9]+(?:-[a-z0-9]+)*", re.ASCII)
HEAD = re.compile(r"[0-9a-f]{40}", re.ASCII)
TOKEN = re.compile(r"Bearer ([A-Za-z0-9_-]{43})", re.ASCII)
RELEASE_REASONS = {
    "abandoned",
    "does_not_elaborate",
    "exhausted",
    "hypothesis_too_weak",
    "missing_lemma",
    "not_a_fit",
    "other",
    "out_of_time",
    "statement_seems_false",
    "superseded",
}


HARNESS_NAMES = (
    'codex',
    'claude-code',
    'cursor',
    'gemini-cli',
    'opencode',
    'kimi-code',
    'qwen-code',
    'qoder',
    'qoder-cn',
    'lingma',
    'trae',
    'codebuddy',
    'comate',
    'codegeex',
    'iflycode',
    'github-copilot',
    'github-copilot-cli',
    'windsurf',
    'cline',
    'roo-code',
    'kilo-code',
    'continue',
    'aider',
    'goose',
    'openhands',
    'kiro',
    'amazon-q',
    'augment-code',
    'auggie',
    'devin',
    'devin-desktop',
    'jetbrains-ai',
    'jetbrains-air',
    'junie',
    'zed',
    'warp',
    'tabnine',
    'replit-agent',
    'factory-droid',
    'mistral-vibe',
    'pi',
    'antigravity',
    'hermes-agent',
    'swe-agent',
    'mini-swe-agent',
    'open-interpreter',
    'other',
    'unknown',
)
AGENT_LABEL = re.compile(r"[a-zA-Z0-9][a-zA-Z0-9 ._:/+\-]{0,95}", re.ASCII)
# Only recognize this explicit family of aliases. Do not strip arbitrary model suffixes:
# dates, preview names, fine-tunes and other providers may encode distinct models there.
GPT_VARIANT = re.compile(
    r"(?:openai[/:])?(?:gpt[ _-]?)?(\d+(?:\.\d+)+)[ _-]+"
    r"(astra|sol|terra|luna)(?:[ _-]*(?:none|minimal|low|medium|high|xhigh|max|ultra))?"
)


def model_ranking_name(value):
    """Group known spelling/effort aliases without changing submitted provenance."""
    label = " ".join(value.lower().split())
    match = GPT_VARIANT.fullmatch(label)
    return f"gpt-{match[1]}-{match[2]}" if match else label


def agent_metadata(value):
    """Normalize self-reported identifiers; missing data stays explicitly unknown."""
    if not isinstance(value, dict) or not {"model", "harness"} <= value.keys():
        raise ValueError("agent_model_and_harness_required")
    if set(value) - {"model", "harness", "harness_version"}:
        raise ValueError("invalid_agent_metadata")
    result = {}
    for key in ("model", "harness", "harness_version"):
        label = value.get(key, "unknown")
        if not isinstance(label, str) or not AGENT_LABEL.fullmatch(label):
            raise ValueError("invalid_agent_metadata")
        result[key] = " ".join(label.lower().split())
    if result["harness"] not in HARNESS_NAMES:
        raise ValueError("invalid_agent_metadata")
    return result


def canonical_handle(value):
    if isinstance(value, str) and value.isascii() and len(value) <= 39 and HANDLE.fullmatch(value.lower()):
        return value.lower()
    return None


def positive_id(value, maximum=(1 << 63) - 1):
    return type(value) is int and 0 < value <= maximum


def fleet_pass(secret, handle, expires):
    message = f"goldbach/fleet/v1/{handle}/{expires}".encode("ascii")
    signature = hmac.new(secret, message, hashlib.sha256).hexdigest()
    return f"v1.{expires}.{signature}"


def error(status, code):
    return status, {"error": code}


class Desk:
    def __init__(self, db_path, gaps, secret):
        self.db_path = db_path
        self.gaps = {gap["id"]: gap for gap in gaps}
        self.statement_hashes = {
            gap_id: hashlib.sha256(gap["statement"].encode("utf-8")).hexdigest()
            for gap_id, gap in self.gaps.items()
        }
        self.secret = secret
        with closing(sqlite3.connect(db_path)) as conn:
            conn.execute("PRAGMA journal_mode=WAL")
            conn.executescript("""
                CREATE TABLE IF NOT EXISTS goldbach_leases (
                    token_hash TEXT PRIMARY KEY,
                    gap TEXT NOT NULL,
                    statement_sha256 TEXT NOT NULL,
                    handle TEXT NOT NULL,
                    ip_key TEXT NOT NULL,
                    claimed_at INTEGER NOT NULL,
                    expires_at INTEGER NOT NULL,
                    absolute_expires_at INTEGER NOT NULL,
                    pr INTEGER,
                    head TEXT,
                    submitted_at INTEGER,
                    run_id INTEGER UNIQUE,
                    checking_at INTEGER,
                    released_at INTEGER,
                    release_reason TEXT,
                    finished_at INTEGER,
                    verdict TEXT CHECK(verdict IN ('ACCEPTED', 'REJECTED'))
                );
                CREATE INDEX IF NOT EXISTS goldbach_leases_ip_time
                    ON goldbach_leases(ip_key, claimed_at);
                CREATE UNIQUE INDEX IF NOT EXISTS goldbach_leases_authorized_head
                    ON goldbach_leases(pr, head) WHERE run_id IS NOT NULL;
            """)
            columns = {row[1] for row in conn.execute("PRAGMA table_info(goldbach_leases)")}
            if "last_polled_at" not in columns:
                conn.execute("ALTER TABLE goldbach_leases ADD COLUMN last_polled_at INTEGER")
            # Additive migration keeps existing leases/verdicts and old clients usable.
            for column in ("model", "harness", "harness_version"):
                if column not in columns:
                    conn.execute(f"ALTER TABLE goldbach_leases ADD COLUMN {column} TEXT NOT NULL DEFAULT 'unknown'")
            if "agent_reported" not in columns:
                conn.execute("ALTER TABLE goldbach_leases ADD COLUMN agent_reported INTEGER NOT NULL DEFAULT 0")

    @contextmanager
    def transaction(self, write=False):
        with closing(sqlite3.connect(self.db_path, timeout=15)) as conn, conn:
            conn.row_factory = sqlite3.Row
            conn.execute("BEGIN IMMEDIATE" if write else "BEGIN")
            yield conn

    def network_key(self, client_ip):
        try:
            addr = ipaddress.ip_address(client_ip)
        except ValueError:
            return None
        addr = getattr(addr, "ipv4_mapped", None) or addr
        network = str(addr) if addr.version == 4 else str(ipaddress.IPv6Network((addr, 64), strict=False))
        return hmac.new(self.secret, b"desk network:" + network.encode("ascii"), hashlib.sha256).hexdigest()

    @staticmethod
    def proved_gaps(conn):
        if not conn.execute("SELECT 1 FROM sqlite_master WHERE type='table' AND name='verdicts'").fetchone():
            return set()
        return {
            row[0] for row in conn.execute("""
                SELECT DISTINCT json_extract(CAST(body AS TEXT), '$.lemma_id')
                FROM verdicts
                WHERE json_extract(CAST(body AS TEXT), '$.verdict') = 'ACCEPTED'
            """)
        }

    @staticmethod
    def lease_times(lease):
        return {key: lease[key] for key in ("expires_at", "absolute_expires_at")}

    @staticmethod
    def token_hash(token):
        return hashlib.sha256(token.encode("ascii")).hexdigest()

    def claim(self, body, client_ip, now, fleet=None):
        handle = canonical_handle(body.get("handle"))
        ip_key = self.network_key(client_ip)
        requested_gap = body.get("gap")
        if not handle or not ip_key or (requested_gap is not None and not isinstance(requested_gap, str)):
            return error(400, "invalid_claim")
        if requested_gap is not None and requested_gap not in self.gaps:
            return error(404, "unknown_gap")
        if requested_gap and self.gaps[requested_gap].get("refutation"):
            return error(409, "refutation_" + self.gaps[requested_gap]["refutation"]["status"])
        if requested_gap and self.gaps[requested_gap].get("claims_closed"):
            return error(409, "claims_closed")
        if fleet is not None:
            match = re.fullmatch(r"v1\.([0-9]{1,12})\.[a-f0-9]{64}", fleet)
            if (not match or int(match[1]) <= now
                    or not hmac.compare_digest(fleet, fleet_pass(self.secret, handle, int(match[1])))):
                return error(401, "invalid_fleet_pass")
            # A registered fleet has its own bucket, including behind a shared university NAT.
            ip_key = "fleet:" + handle
        with self.transaction(write=True) as conn:
            active = conn.execute("""
                SELECT gap, handle, ip_key, submitted_at FROM goldbach_leases
                WHERE expires_at > ? AND released_at IS NULL AND finished_at IS NULL
            """, (now,)).fetchall()
            owned = [lease for lease in active if lease["handle"] == handle]
            handle_count = len(owned)
            # One extra checkout while a registered PR waits for a verdict.
            if fleet is None and (handle_count >= 2 or any(row["submitted_at"] is None for row in owned)):
                return error(409, "handle_already_active")
            if fleet is not None and handle_count >= FLEET_ACTIVE_LIMIT:
                return error(429, "fleet_active_limit")
            if fleet is None and sum(lease["ip_key"] == ip_key for lease in active) >= NETWORK_ACTIVE_LIMIT:
                return error(429, "network_active_limit")
            if conn.execute("""
                SELECT COUNT(*) FROM goldbach_leases WHERE ip_key = ? AND claimed_at > ?
            """, (ip_key, now - 3600)).fetchone()[0] >= (4 * FLEET_ACTIVE_LIMIT if fleet else NETWORK_HOURLY_LIMIT):
                return error(429, "network_claim_limit")

            load = Counter(lease["gap"] for lease in active)
            proved = self.proved_gaps(conn)
            candidates = ((key for key, gap in self.gaps.items() if not gap.get("challenge_only") and not gap.get("claims_closed") and not gap.get("refutation"))
                          if requested_gap is None else (requested_gap,))
            if fleet is None and owned:
                candidates = (gap for gap in candidates if gap != owned[0]["gap"])
            program_load = Counter(self.gaps[row["gap"]].get("program", "foundation")
                                   for row in active if row["gap"] in self.gaps)
            available = (g for g in candidates if g not in proved and
                         (not load[g] or self.gaps[g].get("parallel") is True))
            # Cover unclaimed statements first. Then balance independent attempts on open problems.
            selected = min(available, key=lambda g: (load[g], self.gaps[g].get("role") == "endpoint", program_load[
                self.gaps[g].get("program", "foundation")]), default=None)
            if selected is None:
                return error(409, "no_available_gap")

            token = secrets.token_urlsafe(32)
            expires = now + LEASE_SECONDS
            absolute = now + MAX_RESEARCH_SECONDS
            conn.execute("""
                INSERT INTO goldbach_leases
                    (token_hash, gap, statement_sha256, handle, ip_key, claimed_at, expires_at, absolute_expires_at)
                VALUES (?, ?, ?, ?, ?, ?, ?, ?)
            """, (self.token_hash(token), selected, self.statement_hashes[selected],
                  handle, ip_key, now, expires, absolute))
            return 201, {
                "gap": self.gaps[selected],
                "lease": {"token": token, "expires_at": expires, "absolute_expires_at": absolute},
            }

    def update_lease(self, action, body, authorization, now):
        token = TOKEN.fullmatch(authorization)
        if token is None:
            return error(401, "invalid_lease")
        digest = self.token_hash(token[1])
        with self.transaction(write=True) as conn:
            lease = conn.execute("SELECT * FROM goldbach_leases WHERE token_hash = ?", (digest,)).fetchone()
            if lease is None:
                return error(401, "invalid_lease")
            if lease["released_at"] is not None:
                return (200, {"released": True}) if action == "release" else error(410, "lease_released")
            if lease["finished_at"] is not None:
                return error(410, "lease_completed")
            if lease["expires_at"] <= now:
                return error(410, "lease_expired")

            if action == "beat":
                times = self.lease_times(lease)
                if lease["pr"] is None:
                    times["expires_at"] = min(now + LEASE_SECONDS, lease["absolute_expires_at"])
                    conn.execute("UPDATE goldbach_leases SET expires_at = ? WHERE token_hash = ?",
                                 (times["expires_at"], digest))
                return 200, times
            if action == "release":
                if lease["run_id"] is not None:
                    return error(409, "check_already_started")
                reason = body.get("reason", "abandoned")
                if not isinstance(reason, str) or reason not in RELEASE_REASONS:
                    return error(400, "invalid_release_reason")
                conn.execute("""
                    UPDATE goldbach_leases SET released_at = ?, release_reason = ? WHERE token_hash = ?
                """, (now, reason, digest))
                return 200, {"released": True}

            pr, head = body.get("pr"), body.get("head")
            if not positive_id(pr, 9_999_999) or not isinstance(head, str) or not HEAD.fullmatch(head):
                return error(400, "invalid_pull_request")
            same_submission = lease["pr"] == pr and lease["head"] == head
            if same_submission and "agent" not in body:
                return 200, {"submitted": True, **self.lease_times(lease)}
            try:
                agent = agent_metadata(body.get("agent"))
            except ValueError as exc:
                return error(400, str(exc))
            if lease["pr"] is not None:
                if same_submission:
                    if any(agent[key] != lease[key] for key in agent):
                        return error(409, "submission_metadata_frozen")
                    return 200, {"submitted": True, **self.lease_times(lease)}
                return error(409, "lease_already_submitted")

            # A submitted proof waits for a hosted runner independently of its authoring lease.
            expires = now + SUBMISSION_SECONDS
            conn.execute("""
                UPDATE goldbach_leases SET pr = ?, head = ?, submitted_at = ?, expires_at = ?,
                    model = ?, harness = ?, harness_version = ?, agent_reported = ?
                WHERE token_hash = ?
            """, (pr, head, now, expires, agent["model"], agent["harness"], agent["harness_version"],
                  1, digest))
            return 200, {"submitted": True, "expires_at": expires,
                         "absolute_expires_at": lease["absolute_expires_at"]}

    def signed(self, supplied, raw_body):
        expected = "sha256=" + hmac.new(self.secret, raw_body, hashlib.sha256).hexdigest()
        return hmac.compare_digest(expected.encode("ascii"), supplied.encode("utf-8"))

    def pending(self, now, limit=QUEUE_BATCH):
        with self.transaction(write=True) as conn:
            rows = conn.execute("""
                SELECT token_hash, pr, head, handle, gap FROM goldbach_leases
                WHERE pr IS NOT NULL AND run_id IS NULL AND released_at IS NULL AND expires_at > ?
                  AND (last_polled_at IS NULL OR last_polled_at <= ?)
                ORDER BY last_polled_at IS NOT NULL, last_polled_at, submitted_at, rowid LIMIT ?
            """, (now, now - QUEUE_RETRY_SECONDS, limit)).fetchall()
            conn.executemany("UPDATE goldbach_leases SET last_polled_at = ? WHERE token_hash = ?",
                             [(now, row["token_hash"]) for row in rows])
            return 200, {"pending": [{key: row[key] for key in ("pr", "head", "handle", "gap")} for row in rows]}

    def authorize(self, body, supplied, raw_body, now):
        if not self.signed(supplied, raw_body):
            return error(401, "invalid_signature")

        pr, head, run_id = body.get("pr"), body.get("head"), body.get("run_id")
        handle, gap = canonical_handle(body.get("handle")), body.get("gap")
        statement_hash = body.get("statement_sha256")
        if (not positive_id(pr, 9_999_999) or not positive_id(run_id)
                or not isinstance(head, str) or not HEAD.fullmatch(head)
                or not handle or not isinstance(gap, str)
                or not isinstance(statement_hash, str)):
            return error(400, "invalid_authorization")
        with self.transaction(write=True) as conn:
            lease = conn.execute("""
                SELECT * FROM goldbach_leases WHERE pr = ? AND head = ? AND handle = ? AND gap = ?
                ORDER BY (run_id = ?) DESC, claimed_at DESC, rowid DESC LIMIT 1
            """, (pr, head, handle, gap, run_id)).fetchone()
            if (lease is None or lease["released_at"] is not None
                    or lease["statement_sha256"] != statement_hash
                    or self.statement_hashes.get(gap) != statement_hash):
                return error(409, "no_matching_submission")
            if lease["run_id"] == run_id and lease["expires_at"] > now and lease["finished_at"] is None:
                return 200, {"authorized": True}
            if lease["run_id"] is not None or lease["expires_at"] <= now:
                return error(409, "submission_unavailable")
            if gap in self.proved_gaps(conn):
                return error(409, "gap_already_proved")
            if conn.execute("SELECT 1 FROM goldbach_leases WHERE run_id = ?", (run_id,)).fetchone():
                return error(409, "run_already_authorized")
            if conn.execute("""
                SELECT 1 FROM goldbach_leases WHERE pr = ? AND head = ? AND run_id IS NOT NULL
            """, (pr, head)).fetchone():
                return error(409, "head_already_authorized")

            conn.execute("""
                UPDATE goldbach_leases SET run_id = ?, checking_at = ?, expires_at = ?
                WHERE token_hash = ?
            """, (run_id, now, now + CHECK_SECONDS, lease["token_hash"]))
            return 200, {"authorized": True}

    def dispatch(self, path, body, headers, client_ip, raw_body):
        if not isinstance(body, dict):
            return error(400, "invalid_json")
        now = int(time.time())
        if path == "/api/desk/claim":
            return self.claim(body, client_ip, now, headers.get("X-Goldbach-Fleet"))
        if path == "/api/desk/pending":
            if not self.signed(headers.get("X-Goldbach-Signature", ""), raw_body):
                return error(401, "invalid_signature")
            return self.pending(now)
        if path == "/api/desk/authorize":
            return self.authorize(body, headers.get("X-Goldbach-Signature", ""), raw_body, now)
        if path in {"/api/desk/beat", "/api/desk/release", "/api/desk/submit"}:
            return self.update_lease(path.rsplit("/", 1)[1], body, headers.get("Authorization", ""), now)
        return error(404, "unknown_endpoint")

    @staticmethod
    def record_verdict(record, conn):
        # An accepted rerun supersedes a rejection, while a failed rerun cannot erase credit.
        verdict = record["verdict"]
        now = int(time.time())
        conn.execute("""
            UPDATE goldbach_leases SET finished_at = ?, verdict = ?
            WHERE run_id = ? AND gap = ?
              AND (verdict IS NULL OR (verdict = 'REJECTED' AND ? = 'ACCEPTED'))
        """, (now, verdict, record["run_id"], record["lemma_id"], verdict))

        if verdict == "ACCEPTED":
            conn.execute("""
                UPDATE goldbach_leases SET released_at = ?, release_reason = 'superseded'
                WHERE gap = ? AND released_at IS NULL AND finished_at IS NULL
                    AND run_id IS NULL AND expires_at > ?
            """, (now, record["lemma_id"], now))

    @staticmethod
    def active_assignments(conn, now):
        return dict(conn.execute("""
            SELECT gap, CASE WHEN MAX(run_id IS NOT NULL) THEN 'checking'
                             WHEN MAX(submitted_at IS NOT NULL) THEN 'submitted'
                             ELSE 'working' END
            FROM goldbach_leases
            WHERE expires_at > ? AND released_at IS NULL AND finished_at IS NULL GROUP BY gap
        """, (now,)))

    def progress_snapshot(self):
        with self.transaction() as conn:
            proved = self.proved_gaps(conn) & self.gaps.keys()
            assigned = self.active_assignments(conn, int(time.time()))
        available = sum(
            not gap.get("claims_closed") and not gap.get("refutation") and gap_id not in proved and (gap_id not in assigned or gap.get("parallel") is True)
            for gap_id, gap in self.gaps.items()
        )
        return len(proved), len(self.gaps), available, assigned.keys() - proved

    def progress(self):
        return self.progress_snapshot()[:3]

    @staticmethod
    def annotate_verdicts(records, conn):
        """Attach attribution via the authorized run, without changing signed verdict bytes."""
        for record in records:
            row = conn.execute("""
                SELECT model, harness, harness_version, agent_reported FROM goldbach_leases
                WHERE run_id = ? AND gap = ? AND pr IS NOT NULL AND head IS NOT NULL
            """, (record["run_id"], record["lemma_id"])).fetchone()
            record["agent"] = dict(zip(("model", "harness", "harness_version"), row[:3])) if row else dict.fromkeys(("model", "harness", "harness_version"), "unknown")
            record["agent"]["source"] = "self_reported" if row and row[3] else "unrecorded"

    @staticmethod
    def agent_rankings(conn, now):
        # Same first-acceptance rule as the contributor leaderboard, one attribution per lemma.
        winners = conn.execute("""
            WITH accepted AS (
                SELECT model, harness, finished_at,
                       ROW_NUMBER() OVER (PARTITION BY gap ORDER BY finished_at, run_id) AS position
                FROM goldbach_leases
                WHERE verdict = 'ACCEPTED' AND run_id IS NOT NULL AND finished_at <= ?
            )
            SELECT model, harness FROM accepted WHERE position = 1
                AND (model != 'unknown' OR harness != 'unknown')
        """, (now,)).fetchall()
        def ranking(column):
            counts = Counter(
                model_ranking_name(row[column]) if column == 0 else row[column]
                for row in winners if row[column] != "unknown"
            )
            return [{"name": name, "accepted": count} for name, count in
                    sorted(counts.items(), key=lambda pair: (-pair[1], pair[0]))]
        return {"models": ranking(0), "harnesses": ranking(1), "proofs": len(winners)}

    def public_status(self):
        now = int(time.time())
        with self.transaction() as conn:
            sessions, active = conn.execute("""
                SELECT COUNT(*), COALESCE(SUM(expires_at > ? AND released_at IS NULL AND finished_at IS NULL), 0)
                FROM goldbach_leases
            """, (now,)).fetchone()
            assignments = self.active_assignments(conn, now)
            activities = [
                {key: value for key, value in dict(row).items() if value is not None}
                for row in conn.execute("""
                    WITH events AS (
                        SELECT claimed_at AS at, 'claimed' AS kind, gap AS lemma_id,
                               NULL AS handle, NULL AS pr, NULL AS run_id,
                               NULL AS head_sha, NULL AS reason, 0 AS stage
                        FROM goldbach_leases
                        UNION ALL
                        SELECT submitted_at, 'submitted', gap, NULL, NULL, NULL, NULL, NULL, 1
                        FROM goldbach_leases WHERE submitted_at IS NOT NULL
                        UNION ALL
                        SELECT checking_at, 'checking', gap, handle, pr, run_id, head, NULL, 2
                        FROM goldbach_leases WHERE checking_at IS NOT NULL
                        UNION ALL
                        SELECT released_at, 'released', gap, NULL, NULL, NULL, NULL, release_reason, 3
                        FROM goldbach_leases WHERE released_at IS NOT NULL
                        UNION ALL
                        SELECT finished_at, lower(verdict), gap, handle, pr, run_id, head, NULL, 3
                        FROM goldbach_leases WHERE finished_at IS NOT NULL
                        UNION ALL
                        SELECT expires_at, 'expired', gap,
                               CASE WHEN run_id IS NOT NULL THEN handle END,
                               CASE WHEN run_id IS NOT NULL THEN pr END, run_id,
                               CASE WHEN run_id IS NOT NULL THEN head END, NULL, 3
                        FROM goldbach_leases
                        WHERE expires_at <= ? AND released_at IS NULL AND finished_at IS NULL
                    )
                    SELECT at, kind, lemma_id, handle, pr, run_id, head_sha, reason FROM events
                    ORDER BY at DESC, stage DESC, lemma_id LIMIT 30
                """, (now,))
            ]
            leaderboard = [
                dict(row) for row in conn.execute("""
                    SELECT handle, COUNT(DISTINCT gap) AS accepted FROM goldbach_leases
                    WHERE verdict = 'ACCEPTED' GROUP BY handle ORDER BY accepted DESC, handle LIMIT 20
                """)
            ]
            first_acceptances = [
                dict(row) for row in conn.execute("""
                    WITH accepted AS (
                        SELECT gap, handle, finished_at,
                               ROW_NUMBER() OVER (PARTITION BY gap ORDER BY finished_at, run_id) AS position
                        FROM goldbach_leases
                        WHERE verdict = 'ACCEPTED' AND run_id IS NOT NULL AND finished_at <= ?
                    )
                    SELECT handle, COUNT(*) AS accepted, MAX(finished_at) AS latest_accepted_at,
                           SUM(finished_at >= ?) AS hour_accepted,
                           MAX(CASE WHEN finished_at >= ? THEN finished_at END) AS hour_latest
                    FROM accepted WHERE position = 1 GROUP BY handle
                    ORDER BY accepted DESC, latest_accepted_at DESC, handle
                """, (now, now - 3600, now - 3600))
            ]
            agent_rankings = self.agent_rankings(conn, now)
        all_time = [
            {key: row[key] for key in ("handle", "accepted", "latest_accepted_at")}
            for row in first_acceptances
        ]
        hour = sorted(
            (
                {"handle": row["handle"], "accepted": row["hour_accepted"], "latest_accepted_at": row["hour_latest"]}
                for row in first_acceptances if row["hour_accepted"]
            ),
            key=lambda row: (-row["accepted"], -row["latest_accepted_at"], row["handle"]),
        )
        return {
            "active": active, "sessions": sessions, "assignments": assignments,
            "activities": activities, "leaderboard": leaderboard, "agent_rankings": agent_rankings,
            "rankings": {
                "all_time": all_time,
                "hour": hour,
                "contributors": len(all_time),
                "proofs": sum(row["accepted"] for row in all_time),
                "latest_accepted_at": max((row["latest_accepted_at"] for row in all_time), default=None),
            },
        }
