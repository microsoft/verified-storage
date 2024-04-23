# Project

This repository contains code for verified storage systems. The code is
written in, and its correctness properties are verified with,
[Verus](https://github.com/verus-lang/verus).

Currently, this project contains two crates:

* `pmemlog` implements an append-only log on persistent memory. The
  implementation handles crash consistency, ensuring that even if the process
  or machine crashes, it acts like an append-only log across the crashes. It
  also handles bit corruption, detecting if metadata read from persistent
  memory is corrupted.

* [`multilog`](https://github.com/microsoft/verified-storage/tree/main/storage_node/src/multilog)
  is like `pmemlog` except it implements a collection of append-only logs
  instead of just one. It supports atomically appending to multiple of those
  logs at once.

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
