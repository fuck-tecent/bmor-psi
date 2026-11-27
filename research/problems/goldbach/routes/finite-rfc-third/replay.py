"""Check the finite RFC1 certificates and rational budgets with Python 3."""

import argparse
from bisect import bisect_left
from fractions import Fraction
from hashlib import sha256
from math import factorial, gcd, isqrt, prod
from pathlib import Path

DIRECTORY = Path(__file__).resolve().parent
CUTOFF = 4 * 10**18
WHEEL = 30030
BASES = (17, 19, 23, 181, 29, 37, 41, 43, 31, 47, 53, 67)
EXTRA_PRIMES = (17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73)
LIMIT = 19_495_926_503
Q = 105


def verify(condition, message):
    if not condition:
        raise ValueError(message)


def rows(name, digest):
    certificate = (DIRECTORY / name).read_bytes()
    verify(sha256(certificate).hexdigest() == digest, f"Unexpected digest for {name}")
    return [tuple(map(int, row.split(","))) for row in certificate.decode("ascii").splitlines()]


def trial_prime(n):
    return 2 <= n and all(n % d for d in range(2, isqrt(n) + 1))


def prime_pairs():
    nodes = rows("lucas.csv", "b2a38d52a87ba7f3efe9f110769ef158f70915d7158e22f54a39388626a90860")
    prime_nodes = {2}
    anchors = []
    previous = 2
    for p, base, *factors in nodes:
        verify(previous < p, f"Out-of-order node {p}")
        verify(prod(factors) == p - 1 and all(q in prime_nodes for q in factors), f"Invalid factors for {p}")
        verify(pow(base, p - 1, p) == 1, f"Fermat test failed at {p}")
        for q in set(factors):
            residue = pow(base, (p - 1) // q, p)
            verify(gcd(residue - 1, p) == 1, f"Lucas test failed at {p} and {q}")
        prime_nodes.add(p)
        previous = p
        if CUTOFF - 4095 <= p < CUTOFF + 32768:
            anchors.append(p)
    verify(len(prime_nodes) == 4351 and len(anchors) == 858, "Unexpected certificate size")

    pairs = []
    for n in range(CUTOFF + 130, CUTOFF + 32769, 2):
        index = bisect_left(anchors, n) - 1
        for p in reversed(anchors[max(0, index - 28):index + 1]):
            q = n - p
            if trial_prime(q):
                pairs.append((n, p, q))
                break
        else:
            raise ValueError(f"No pair recorded for {n}")
    csv = "".join(f"{n},{p},{q}\n" for n, p, q in pairs)
    digest = sha256(csv.encode("ascii")).hexdigest()
    verify(digest == "5d510f2aeac701bce09653cdc8796a07791622f76904636cbebd46c00aaa4870", "Unexpected pair digest")
    verify(len(pairs) == 16_320 and len({p for _, p, _ in pairs}) == 767, "Unexpected pair count")
    return csv


def exp_upper(x):
    partial = sum(x**k / factorial(k) for k in range(25))
    return partial + x**25 / factorial(25) / (1 - x / 26)


def verify_wheel():
    wheel = rows("wheel.csv", "d57127f950d88c642bba0788c71d8c462343550505ce7330899c74cc8b328355")
    verify(len(wheel) == len(BASES), "Unexpected wheel size")
    for b, row in zip(BASES, wheel, strict=True):
        verify(gcd(b, WHEEL) == 1 and len(row) == 16, f"Invalid wheel base {b}")
        verify(all(p <= LIMIT and p % WHEEL == b and trial_prime(p) for p in row), f"Invalid lift for {b}")
        verify(all(len({p % q for p in row}) == 16 for q in EXTRA_PRIMES), f"Repeated residue for {b}")
    verify(all(any(gcd(n-b, WHEEL) == 1 for b in BASES) for n in range(0, WHEEL, 2)), "Wheel has an uncovered base")
    verify(tuple(p for p in range(17, 79) if trial_prime(p)) == EXTRA_PRIMES, "Inconsistent list of extra primes")
    verify(exp_upper(Fraction(19, 5)) < 45, "Failed comparison for exp(19/5)")
    verify(exp_upper(Fraction(5)) < Fraction(297, 2), "Failed comparison for exp(5)")
    log_lower = Fraction(546, 125)
    verify(exp_upper(log_lower) < 79, "Failed comparison for log(79)")
    verify(45 < 11*log_lower and Fraction(297, 2) < 34*log_lower, "Failed factor bound")
    verify(LIMIT + 2 < 11**11, "Failed small-range handoff")


def verify_arc_budgets():
    totient_sum = Fraction(0)
    favored = Fraction(0)
    adverse = Fraction(0)
    discretization = Fraction(0)
    costs = {}
    for q in range(1, Q + 1):
        phi = sum(gcd(a, q) == 1 for a in range(q))
        primes = [p for p in range(2, q + 1) if trial_prime(p) and q % p == 0]
        if all(q % (p*p) for p in primes):
            totient_sum += Fraction(1, phi)
            discretization += 4 * Fraction(22, 7) * Fraction(Q, q)**2 / phi
            if 30 % q == 0:
                favored += (1 - Fraction(2*q, 9*Q)) / phi
            else:
                adverse += Fraction(1, phi * min(p-1 for p in primes if 30 % p))
        c = 2 if q <= 2 else 1
        alpha = Fraction(c, 840*42) + Fraction(1, 10**8)
        delta = Fraction(c*Q*22, 7*840*34*q)
        costs[q] = 2*Q*phi*(alpha**2 + alpha*delta + delta**2/3)
    verify(totient_sum == Fraction(40089709476281, 6701240145600), "Unexpected totient sum")
    verify(favored == Fraction(26, 7) and adverse < Fraction(201, 1000), "Failed signed model table")
    verify(discretization < 236336, "Failed discretization budget")
    verify(favored - adverse - discretization/CUTOFF > Fraction(7, 2), "Failed model floor")
    verify(totient_sum + discretization/CUTOFF < 6, "Failed model energy bound")
    small_exp_bound = Fraction(201, 10)
    verify(exp_upper(Fraction(3)) < small_exp_bound, "Failed comparison for exp(3)")
    verify(small_exp_bound**14 < CUTOFF and small_exp_bound**10 * 55 < 6 * 10**14,
           "Failed logarithm lower bounds")
    verify(exp_upper(Fraction(4)) < 55, "Failed comparison for exp(4)")
    verify(21**6 * 55 < 8 * 10**9, "Failed BMOR start logarithm bound")
    verify(3*45*Q < Fraction(CUTOFF, 10**9), "Failed nonunit error allowance")
    energy = sum(costs.values())
    verify(energy < Fraction(3, 40), "Failed major-arc error energy budget")
    print(f"Conditional fixed-arc energy coefficient {float(energy):.9f}")
    for q in sorted(costs, key=costs.get, reverse=True)[:3]:
        print(f"  q={q}: {float(costs[q]):.9f}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--pairs", type=Path, help="Write the regenerated prime pairs as CSV")
    args = parser.parse_args()
    csv = prime_pairs()
    verify_wheel()
    verify_arc_budgets()
    if args.pairs:
        args.pairs.write_bytes(csv.encode("ascii"))
    print("Verified 4351 Lucas nodes, 16320 prime pairs, 192 wheel lifts and the rational arc budgets.")


if __name__ == "__main__":
    main()
