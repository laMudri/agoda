# a碁da – formalising go in Agda
This aims to be a library implementing the rules of [wéiqí/igo/baduk](https://en.wikipedia.org/wiki/Go_(board_game)), allowing us to prove properties of game states.
For example, I would like to prove that any shape with two sufficiently small eyes is alive.

The rules to be implemented are the [Tromp-Taylor rules](https://www.cs.cmu.edu/~wjh/go/tmp/rules/TrompTaylor.html), which have area scoring, positional superko, and no dead stone removal.
I might also require white passing last, depending on how things go.

The project is structured as follows.
`Igo` contains definitions and proofs of anything immediately go-related.
Other modules provide things to extend the standard library.
Of particular note is `Enum`, defined in `Relation.Unary.Enum`, where `Enum P` is an exhaustive finite listing of all values satisfying `P`.
Also commonly used is `Rats` from `Data.Star.Rats`, which is the backwards version of `Star` (reflexive-transitive closure).
In a graph with edges `E`, `Rats E s v` is the type of paths starting at `s` and ending at `v` which are extended at the `v` end.

The [standard library](https://github.com/agda/agda-stdlib) is the only dependency.

The current problem is to find a group of connected stones from a given stone.
This is a special case of finding a connected component of a graph given a vertex in it, which I am trying to solve in `Relation.Binary.Graph`.
