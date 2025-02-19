# Filter-Method Construction for Real Numbers

This project is dedicated to implement the formal proof of a specific real number theory, which was firstly mentioned by Prof.Wang in \[1\], 
then introduced in one of his monographs \[3\] published in 2018.
This mathematical theory employs a special filter, named “non-principal arithmetical ultrafilter (NPAUF)” \[2\], to facilitate the construction of real numbers.
In this project, we refer to it as the “Filter-Method Construction for Reals (FMCR)”.
The proof is implemented in the Coq proof assistant, and grounded in Morse-Kelley axiomatic set theory (MK).
The formalization is mainly guided by Wang's book \[3\].

The construction involves the non-standard extension of number systems.
With the use of NPAUF, the set of natural numbers *ω* can be extended to the non-standard natural number set ***N**, 
which is an useful non-standard model that has simple construction and superior properties \[1\].
***N** includes some special elements at infinity that can be named as infinity natural numbers.
Infinity numbers are greater than all natural numbers (infinitely large) but follow the general arithmetic properties (addition, multiplication, order, etc.) of natural numbers.
Following the idea of equivalence classification, ***N** can be further extended to the non-standard integer set ***Z** inclusive of infinity integers,
and the non-standard rational number set ***Q**, which encompasses both infinity and infinitesimal numbers (numbers that are infinitely small).
The structure of real numbers is then obtained by equivalently classifying a specific subset of ***Q**.

This repository is an extension and continuation of [Formal-verification-of-the-existence-of-non-principal-arithmetical-ultrafilters-in-Coq]([https://github.com/styzystyzy/Axiomatic_Set_Theory/](https://github.com/1DGW/Formal-verification-of-the-existence-of-non-principal-arithmetical-ultrafilters-in-Coq)).

The code is developed in the CoqIDE (version 8.13.2) for 64 bit Windows and can be run at this version or higher ones.
CoqIDE (version 8.13.2) is available at [here](https://github.com/coq/platform/releases/download/2021.02.1/coq-platform-2021.02.1-installer-windows-x86_64.exe).
For other versions of Coq, click [here](https://coq.inria.fr/download).

# Files
The formalization consists totally of 18 \(.v\)files. The file **dependencygraph.pdf** shows the dependency of the files.
The file **instruction.pdf** is edited to introduce how to use (.v)files in CoqIDE.

# Authors
This project is mainly implemented by Guowei Dou<dgw@bupt.edu.cn> and Wensheng Yu<wsyu@bupt.edu.cn>.

Beijing Key Laboratory of Space-ground Interconnection and Convergence, School of Electronic Engineering, Beijing University of Posts and Telecommunications, Beijing

# Main References
\[1\] Wang F. On a special kind of points in stone-cech compactification *βω*. Journal of China University of Science and Technology, 1998, 28(5): 567–570 https://www.doc88.com/p-6798991182725.html

\[2\] Wang F. A result on arithmetical ultrafilters. Journal of China University of Science and Technology, 2000, 30(5): 517–522 https://www.doc88.com/p-2475987732131.html

\[3\] Wang F. Mathematical Foundations, 2nd edn (in Chinese). Beijing: Higher Education Press, 2018

