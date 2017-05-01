Group:
Regina Burd - rburd
Nova Fallen - nfallen

Execution: 

The program is executed from Main.hs. Here the user will be able to enter a regular expression and
choose whether to derive a DFA for this expression via the thompson or brzozowski construction. If
the regular expression is successfully parsed and the DFA is successfully created, the user will be able
to enter a string to see if it is accepted by the DFA. Here the user will also have the option of simply executing
the DFA until it reaches the end result, or invoking the DFA stepper to execute the DFA character by character.

Code Organization:

Outside of the main method, Main.hs also contains the source code for the DFA stepper. 

Regex.hs defines the RegExp data type for regular expressions, along with any other functions 
utilized to parse regular expressions.

Alpha.hs holds the 'Alpha' data type, which defines a non-empty set of characters. It also holds 
helper functions used to manipulate this type.

The Automata class (to which both DFA and NFA instances belong) is defined in Automata.hs, 
along with the stateBijections helper method, which determines all mapping permutations between state sets.

The source code for the DFA data type and the methods to manipulate it are located in the DFA.hs file. 

The source code for the NFA data type and the methods to manipulate it are located in the NFA.hs file.

The code to create an NFA using the thompson construction algorithm, along with methods to convert the 
resulting NFA to a DFA, and to minimize the resulting DFA are located in the Construction.hs file. 
Construction.hs also holds the source code for the brzozowski construction.   

Tests.hs contains unit tests and quickcheck properties testing the correctness of the code. 

Comparison.hs's main function is used to compare the execution times of the thompson and brzozowski constructions with
various inputs, and generates other statistics. Comparison.hs can also generate graphs through the use of the --output flag.


Dependencies: 
cabal install parsec
cabal install set-monad
cabal install criterion
