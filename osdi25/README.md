# PoWER Artifact

This directory contains the files needed to replicate experiments from the
OSDI 2025 paper "PoWER Never Corrupts: Tool-Agnostic Verification of Crash
Consistency and Corruption Detection" by Hayley LeBlanc, Jacob R. Lorch, Chris
Hawblitzel, Cheng Huang, Yiheng Tao, Nickolai Zeldovich, and Vijay
Chidambaram.

This artifact contains information about how to reproduce results from our two verified storage systems, CapybaraNS and CapybaraKV, as well as how to check our proofs of soundness for the prophecy model of storage and PoWER itself.
It is organized as follows:
1. `capybaraNS/` contains CapybaraNS's source code and instructions on how to build/verify/run the system.
2. `capybaraKV` contains instructions on how to build and verify CapybaraKV and how to set up and run the experiments described in Section 6 (Evaluation) of the paper.
3. `soundness_proofs/` contains information about the soundness proofs and how to check them.

Some of the results in this paper take a long time to reproduce. 
Here is a rough estimate of how much time it takes to run the experiments in each part.

1. CapybaraNS: 10-15 minutes total
   1. Initial setup: ~5 minutes
   2. Verifying CapybaraNS and getting line counts: <5 minutes
   3. Running CapybaraNS: ~30 seconds
2. CapybaraKV: ~14 hours total
   1. Initial setup: ~30 minutes
   2. Verifying CapybaraKV and getting line counts: ~5-10 minutes
   3. Running recommended kick-the-tires mini experiments: ~20 minutes
   4. Running all full experiments: ~12 hours (one 4-hour experiment, one 8-hour experiment)
   5. Processing data: ~15 minutes
3. Soundness proofs: 2/3 soundness proofs are checked when verifying CapybaraKV. The third is checked by building Perennial locally and/or checking the status of its CI on GitHub; building Perennial locally can take ~2-3 hours depending on your setup. See this section's [README](soundness_proofs/README.md) for more info.