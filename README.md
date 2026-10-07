# Formal Verification of the Backdoor Adjustment Formula

This code contains the Rocq proofs discussed in a MIT Master's Thesis, which can be found here: <https://adam.chlipala.net/theses/giniya.pdf>

Generally, it contains proofs of the backdoor adjustment formula in two and three variable cases in the file TwoVarThreeVarExamples.v, which corresponds to Chapter 2. It contains proofs of the parental and backdoor adjustment formula in GeneralParentalAdj.v, which corresponds to Chapter 3. And it contains applications of the backdoor adjustment formula to science experiments in ScienceExp.v, which corresponds to Chapter 4. GeneralFormulas.v has some simple math and probability formulas that are used by the other files.