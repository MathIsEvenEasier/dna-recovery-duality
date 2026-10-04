Recovery balance is preserved by duality
=======================================

For every linear code C of length n >= 1, under independent uniform
sampling of encoded coordinates with replacement, the expected numbers
of reads needed to recover coordinate i satisfy::

    a_i(C) + a_i(C^perp) = n.

Consequently, C is recovery balanced if and only if its orthogonal dual is
recovery balanced. This answers Conjecture 1 of Gruica, Bar-Lev, Ravagnani
and Yaakobi, *A Combinatorial Perspective on Random Access Efficiency for
DNA Storage*, under the stated sampling model.

Proof in three steps: https://mathiseveneasier.github.io/dna-recovery-duality/

Conjecture source: https://arxiv.org/html/2401.15722v3#S5.SS3

The argument
------------

1. Keep the target coordinate i aside and partition the other coordinates
   into S and U. Exactly one of these two observations recovers the target:
   S in C, or U in C^perp. If d is the failure indicator, linear duality gives
   d_C(i,S) + d_Cperp(i,U) = 1.

2. The expected recovery time is the sum of d_C(i,S)/choose(n-1,|S|)
   over S not containing i. A particular set of s distinct indices occurs
   with probability 1/choose(n,s), and the conditional mean wait for the
   next new index is n/(n-s). Their product is 1/choose(n-1,s), including
   the cost of repeated reads.

3. Complementary sets have equal weights. Pairing the two sums replaces
   their failure indicators by 1. Each subset size contributes 1; the n
   sizes from 0 to n-1 therefore give a_i(C) + a_i(C^perp) = n. One profile
   is constant exactly when the other is constant.

Read and check
--------------

* recovery-duality.tex: complete mathematical proof, model and references.
* docs/index.html: the three-step explanation.
* lean/CodeResult.lean: the main code theorem and balance equivalence.
* lean/CodeLinear.lean: actual orthogonal dual and complementary recovery.
* lean/CodeGenerator.lean: equivalence with generator-column recovery.
* lean/CodeProbability.lean: exact uniform failure-word probabilities.
* evidence/: recorded compiler output and negative-control rejection.
* verification-code-azure.json: proof scope, source hashes and audit results.
* REPRODUCE.txt: pinned compiler procedure and trust boundary.

A lightweight check needs only Python 3::

    python3 verify_packet.py

It checks file hashes and consistency of recorded evidence; it does not run
Lean. Rebuild with Lean 4.34.0 and mathlib revision
5ed2965256430c3649e86755f9576b54eca72435 as described in REPRODUCE.txt
for independent proof checking.

Formal verification
-------------------

All 13 positive modules passed in the recorded Azure build. The eleven
code declarations audited depend only on propext, Classical.choice and
Quot.sound. An intentionally invalid proof of False was rejected. The
proof sources contain no custom axioms, admitted goals, unsafe declarations
or native_decide. Both negative-control files are deliberately invalid and
must be excluded from the positive build.

The Lean result quantifies over arbitrary fields and finite nonempty
coordinate sets. Expected reads are defined by a proved-convergent tail
sum of exact uniform failure-word probabilities. The certificate proves
orthogonal-code duality and the generator-column recovery characterization.
A separate infinite-sequence probability space and hitting-time random
variable are not constructed in Lean. The usual probabilistic
interpretation is given in the written proof.

The written EXIT and Shapley interpretations and the alternative zero-time
convention are outside the Lean certificate. The recorded verification
uses the standard Lean kernel and pinned upstream mathlib cache artifacts;
no independent kernel implementation audit was performed for this result.
The formal statement has not received an independent human audit. This
repository is a research announcement, without external peer review.

Model and use
-------------

These are encoded-coordinate recovery times. A coordinate known to be zero
requires no reads. The note separately handles the convention requiring a
first read even for a known zero; the balance equivalence survives, while
the coordinatewise sum needs a correction at such coordinates.

A recovery profile for C immediately gives the entire profile for C^perp.
Balance transfers, coordinate ordering reverses, and an exactly self-dual
code has expected recovery time n/2 at every coordinate. These statements
apply to the uniform error-free read model; they do not assert a physical
sequencing speedup or an improvement in decoding runtime.

Sources and attribution
-----------------------

The proof uses established linear algebra and sampling identities. The
note also derives a_i/n as the coordinate EXIT area and relates the result
to classical EXIT duality, crediting Ashikhmin, Kramer and ten Brink (2004)
and Renes (2017/2018):

* https://doi.org/10.1109/TIT.2004.836693
* https://arxiv.org/html/1701.05583v2

Prepared by MathIsEvenEasier with OpenAI Codex (GPT-6 Astra).
Research inspired by @xamualexander, Dr. Samuel Allen Alexander. Still there.
