## Installing UniMath (Coq)

Exercises can be done on paper or using the UniMath library in the Coq proof assistant. (Or other libraries in other proof assistants if you dare!) Here are instructions for installing/using the UniMath library in the Coq proof assistant in order from easiest to hardest.

1. Use an in-browser implementation: https://unimath.github.io/live/
  - This has been recently put together. I've tested it with the exercises, and it works great for me with Chrome on MacOS (but not Safari). If there are any problems, it would be appreciated if you could report them here: https://github.com/UniMath/UniMath/discussions/1729.

2. Use the UniMath binaries provided with recent distributions of Coq + VSCode: https://docs.google.com/document/d/1KWSugPK-sJ67pL-P4EtoKZ6HMzewmzewLNkR_arXauY/edit?usp=sharing
  - Note that where there are paths like `/Applications/Coq-Platform~8.15~2022.04.app/Contents/Resources/bin` you need to check that this is where Coq is installed on your computer. In particular, if you have installed it recently, it will be something more like `Coq-Platform~8.16~2022.09.app`.
  - To easily type unicode symbols, install the "Unicode Latex" extension for VSCode.
  - Also make sure that the custom VS Code settings are not being applied whenever you want to work with vanilla Coq. This should be the case because the instructions have you apply them to a particular workspace.

3. Compile UniMath yourself + use Emacs: https://github.com/UniMath/UniMath/blob/master/INSTALL.md