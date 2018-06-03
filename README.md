# compositional-typing

Exploration of compositional typing, and better type error messsages, implemented using relational type inferencers written in miniKanren.

Joint work between Kanae Tsushima and Will Byrd, inspired by the FLOPS 2018 paper:

Tsushima K., Chitil O. (2018) A Common Framework Using Expected Types for Several Type Debugging Approaches. In: Gallagher J., Sulzmann M. (eds) Functional and Logic Programming. FLOPS 2018. Lecture Notes in Computer Science, vol 10818. Springer, Cham

which in turn builds on the work in:

Olaf Chitil. 2001. Compositional explanation of types and algorithmic debugging of type errors. In Proceedings of the sixth ACM SIGPLAN international conference on Functional programming (ICFP '01). ACM, New York, NY, USA, 193-204. DOI=http://dx.doi.org/10.1145/507635.507659

http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.25.818


Racket Files:

* `types.rkt` contains a simple type inferencer for a Scheme-like language, written as a relation in miniKanren.

* `types-not.rkt` contains a simple type inferencer that only accepts/generates syntactically-valid expressions that *do not* typecheck, according to the rules in `types.rkt`

* `compositional-typing.rkt` contains the beginning of an implementation of the typing rules in the ICFP 2001 paper, with the intent of ultimately implementing the rules from the FLOPS 2018 paper.