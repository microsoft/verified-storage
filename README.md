# Project

This repository contains code for verified storage systems. Most of the code
is written in, and its correctness properties are verified with,
[Verus](https://github.com/verus-lang/verus).

For the artifact associated with our OSDI 2025 paper, "PoWER Never Corrupts:
Tool-Agnostic Verification of Crash Consistency and Corruption Detection", go
to the directory `osdi25` in the `osdi25-artifact` branch.

This project contains the following: 

* `pmemlog` implements a persistent-memory append-only log. It handles crash
  consistency, ensuring that even if the process or machine crashes, it acts
  like an append-only log across the crashes. It also handles bit corruption,
  detecting if metadata read from persistent memory is corrupted.

* `multilog` is like `pmemlog` except it implements a collection of logs, each
  in its own region of persistent memory. Its transactional interface allows
  atomically committing appends across those logs.
  
* `capybaraKV` is a persistent-memory key-value store, handling crash
  consistency and bit corruption.

* `capybaraNS` is a persistent-memory notary service, written in Dafny and
  using the PoWER specification approach described in the OSDI 2025 paper.
  
* `unverified` contains unverified mocks and tests.

* `soundness_proofs` contains formalized arguments of soundness for the PoWER
  specification approach used to prove crash consistency.

## Contributing

This project welcomes contributions and suggestions.  Most contributions require you to agree to a
Contributor License Agreement (CLA) declaring that you have the right to, and actually do, grant us
the rights to use your contribution. For details, visit https://cla.opensource.microsoft.com.

When you submit a pull request, a CLA bot will automatically determine whether you need to provide
a CLA and decorate the PR appropriately (e.g., status check, comment). Simply follow the instructions
provided by the bot. You will only need to do this once across all repos using our CLA.

This project has adopted the [Microsoft Open Source Code of Conduct](https://opensource.microsoft.com/codeofconduct/).
For more information see the [Code of Conduct FAQ](https://opensource.microsoft.com/codeofconduct/faq/) or
contact [opencode@microsoft.com](mailto:opencode@microsoft.com) with any additional questions or comments.

## Trademarks

This project may contain trademarks or logos for projects, products, or services. Authorized use of Microsoft 
trademarks or logos is subject to and must follow 
[Microsoft's Trademark & Brand Guidelines](https://www.microsoft.com/en-us/legal/intellectualproperty/trademarks/usage/general).
Use of Microsoft trademarks or logos in modified versions of this project must not cause confusion or imply Microsoft sponsorship.
Any use of third-party trademarks or logos are subject to those third-party's policies.
