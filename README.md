intuitRGC - page under construction -
=========

An efficient SAT-based theorem prover for Intuitionistic Propostional Logic using general clauses.



References
----------


[1] C. Fiorentini, M. Ferrari. General Clauses for SAT-based Proof-search in Intuitionistic Propositional Logic. Submitted.



Haskell installation
-------------------

You have to install the [Haskell toolchain](https://www.haskell.org/downloads)
(see  the section  [Installation instructions](https://www.haskell.org/downloads#ghcup)), 
in particular:

- [GHC](https://www.haskell.org/ghc/): the Glasgow Haskell Compiler
- [cabal-install](https://cabal.readthedocs.io/en/3.6/): the Cabal installation tool for managing Haskell software.



IntuitRGC compilation
----------------------

From the  root directory (i.e., the directory containing the file  `intuitRGC.cabal`) run the command:

```console
 cabal install
```

It should be printed a message like this:

```console
 ....
 Symlinking 'intuitRGC' to '/myHome/.cabal/bin/intuitRGC'
```

This means that `intuitRGC` is the command to launch the prover. Actually,
`intuitRGC` is a symbolic link to    `/myHome/.cabal/bin/intuitRGC`; if
the command `intuitRGC` is not found you have to add the directory `/myHome/.cabal/bin/` to
your `PATH` variable (or write the complete path of the command).


To print the usage help:


```console
intuitRGC -h
```


Running
-------

The input formula must be written in a text file. A formula `F` is specified by the following syntax:

```console
  F :=     atom          // prop. variable
        |  $false        // false
        |   ~F           // not 
        |  F & F         // and
        |  F | F         // or
        |  F -> F        // implication
	|  F => F        // implication
	|  F <-> F       // bi-implication
        |  F <=> F       // bi-implication
```
Examples of formulas:

```console
(a => b) | ( b => a )
a | (a- b | ~b)
~ a | ~~a
(a | b) <-> (b | a)
( ((a1 <=> a2) =>  a1 & a2 & a3) & ((a2 <=> a3)  =>  a1 & a2 & a3)  & (( a3 <=> a1)  => a1 & a2 & a3 ) )  =>  a1 & a2 & a3  
```

You can also use the [TPTP syntax](http://tptp.cs.miami.edu/TPTP/QuickGuide/Problems.html).
Examples of formulas are available in the directory [test](https://github.com/cfiorentini/intuitRGC/tree/main/test)
(files with suffix `.p`).


Sequents 
--------

You can run the prover check the validity/countersatisfiability  of a sequent (option `-c`); the sequent must be written in the input file using the following syntax.

A  general clause has the form

```console
 d1 | d2| ... | ~c1| ~c2 | a1 =/=> b1 |   a2 =/=> b2 | ...
```
where:

-  a1, a2, ...  c1, c2 ...  d1, d2 ... are atoms
-  b1, b2 ... are atoms or $false
-   =/=> can be replaced by  # or -/->

A sequent has the form

```console
 gc1 , gc2  , ... , gcn ==>  g
```

where g is an atom or $false. 


Example of sequent:


```console
a1 =/=> b2 | a2 =/=> a3 , ~a1 | a1 , ~a2 | a3 ==> g

```


The sequent in Example 1 can be codified as follows:

```console
a | ~c ,
b | ~c ,
d | g ,
g | a  =/=> b , 
g | b  =/=> a , 
~d | c  =/=> q 
==> g
```


