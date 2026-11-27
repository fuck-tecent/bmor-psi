"""Track unconditional large-prime-factor theorems for n² + 1."""

from fractions import Fraction


BASELINE = {
    "exponent": "1.323",
    "kind": "external_certificate",
    "source_url": "https://github.com/CGandGameEngineLearner/landau-fourth-problem-1.323/"
                  "blob/42cd8945093d9c82379dc9193b2e5fb6c8758c78/README.md",
}


def record_statement(exponent):
    power = Fraction(exponent)
    if not 0 < power <= 2:
        raise ValueError(f"Exponent outside the Landau track: {exponent}")
    return ("∀ B : ℕ, ∃ n p : ℕ, B < n ∧ Nat.Prime p ∧ p ∣ n ^ 2 + 1 ∧ "
            f"n ^ {power.numerator} < p ^ {power.denominator}")


def exponent_record(desk, conn):
    # authorize() binds the hash of the frozen CI statement to the lease/run.
    # record_verdict() sets ACCEPTED only after the signed report for that run.
    accepted = {(gap, digest): run_id for gap, digest, run_id in conn.execute("""
        SELECT gap, statement_sha256, MIN(run_id) FROM goldbach_leases
        WHERE kind = 'prove' AND verdict = 'ACCEPTED' AND run_id IS NOT NULL
        GROUP BY gap, statement_sha256
    """)}
    composed = {gap: digest for gap, digest in conn.execute(
        "SELECT gap,json_extract(certificate,'$.statement_sha256') FROM assembled_proofs")}
    verified = None
    for gap in desk.gaps.values():
        exponent = gap.get("lpf_exponent")
        if exponent is None:
            continue
        if gap["statement"] != record_statement(exponent):
            raise ValueError(f"Unexpected record statement for {gap['id']}")
        run = accepted.get((gap["id"], desk.statement_hashes[gap["id"]]))
        assembled = composed.get(gap["id"]) == desk.statement_hashes[gap["id"]]
        if (run is not None or assembled) and (verified is None or Fraction(exponent) > Fraction(verified["exponent"])):
            verified = {
                "exponent": exponent,
                "kind": "lean_accepted",
                "source_url": (f"https://github.com/CGandGameEngineLearner/goldbach-proofs/actions/runs/{run}"
                               if run is not None else "https://www.movan.tech/goldbach/problems/quadratic-primes/?lemma=" + gap["id"]),
            }
    current = BASELINE
    if verified and Fraction(verified["exponent"]) >= Fraction(BASELINE["exponent"]):
        current = verified
    return {"baseline": BASELINE, "target": "2", "current": current, "verified": verified}
