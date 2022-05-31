# Logika v računalništvu student project polynomials

This repository contains formalization of polynomials in agda:

* `project/`: contains all of the agda code

Files to look after are:

* `project.agda`: Contains definition of a ring, some properties of ring, definition of Polynomials and operations + and * on them.
In this file one can also find unfinished proof for commutativity of * on polynomials. The proof is turning out to be tedious since  
agda forgets already computed values (like that some variable is nonzero). Rewriting does not always work (or we are doing something wrong). Additionaly 'cong' also does not act very smart, since we have to put implicit arguments to it often by force (which is annoying when we have long expressions as arguments). At the end of file is a simple example of a ring $Z_2$ and a few test cases. 

* `noviplus2.agda`: This file contains duplicate of definitions of operations and ring. Additional ring properties are proved. Then follows proof of commutativity for + and not so succesful proof for asociativity of +.  At the end there is proof that $-_p$ operation is inverse for polynomial addition.