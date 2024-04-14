# Cinderella vs. Stepmother
This repository tries to solve the Cinderella-Stepmother game using Game Theory on Infinite Graphs efficiently.

## Game Description
There are two players, Cinderella and the Stepmother. The game is played using
5 buckets that are arranged in a circle. Each bucket is initially empty. 
Additionally, we fix a constant `c > 0` that represents the volume of the
buckets.

The game is played in turns. The stepmother goes first. She can choose to
divide 1 unit of water into arbitrary parts and pour them into the buckets.
Then, Cinderella can choose 2 consecutive buckets and pour the water from them
out.

The stepmother wins if she can make one of the buckets overflow. Cinderella
wins if she can prevent this from happening.


## Relevance
The game has relevance in the context of formal verification of systems. More
specifically, it can be interpreted a reachability game with the question 
whether the stepmother can reach a state where one of the buckets overflows. It
can also be seen as a safety game where the question is whether Cinderella can 
prevent the stepmother from reaching such a state.

