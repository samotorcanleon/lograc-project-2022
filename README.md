# Logika v računalništvu student project Polynomials

This repository contains formalization of polynomials in agda:

* `project/`: contains all of the agda code

Files someone will find in `project/` are :

* `Ring.agda`: contains definition of a ring

* `RingProperties.agda`: contains proofs for properties of a ring which are used when proving properties of polinomials.

* `Polynomials.agda`: contains definition of Polynomial type and the following operations on polynomials: addition, inverse for addition, multiplication and degree.

* `PolynomialsProperties.agda`: contains all sorts of proofs regarding polynomials. Among other things the most important are proof of commutativity of addition and even more commutativity of multiplication.

* `Z2.agda`: implementation of ring $Z_2$ with test cases for polynomials over $Z_2$.

* `Z5.agda`: implementation of ring $Z_5$ with test cases for polynomials over $Z_5$.

