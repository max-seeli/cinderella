from  gensys.helper import *
from  gensys.fixpoints import *
from z3 import *

# Robot cocktail game, where a robot tries to mix a cocktail consisting of two liquids, a and b.
# Specification: Reachabality, F And(a >= 0.0, b >= 0.0 , a + b >= 9 , a >= 9 * b - 1)

# 0. Define game type (Int/ Real)
game_type = "Real"

fill_speed = 1
spill_amount = 0.2
spill_per_liquid = spill_amount / 2.0

# 1. Define Environment moves
def spill(a, b, a_, b_):
    return And(a_ <= a, b_ <= b, a_ >= a - spill_per_liquid, b_ >= b - spill_per_liquid)

#2. Define Controller moves

def add(a, b, a_, b_):
    return And(a_ >= a, b_ >= b, (a_ - a) + (b_ - b) <= fill_speed)


# 3. Define Init Region (False by default => Maximal winning region will be returned)

def init(a, b):
    return And(a == 1.0, b == 1.0)

spec_type = sys.argv[1]

if spec_type == "simple":
    # Dual game must taken into account environment being the first player but playing second! i.e. game mode = 1 and game = reachability

    def guarantee_reach(a, b):
        return And(a >= 0.0, b >= 0.0, a + b > 10.0, a == 9 * b)

    reachability_fixedpoint_gensys([add], spill, guarantee_reach, 0, game_type, init)

else:
    # If automaton is deterministic, same automaton is enough for both buchi and cobuchi product fixpoints. 
    # If final states are X, just run GF(X) and FG(X) on them to get results for buchi and cobuchi respectively.

    if spec_type == "product-buchi":

        raise NotImplementedError("Product Buchi fixpoint not implemented for this benchmark.")
        # Complete Deterministic Buchi Automaton for the above specification
        # Functions such as automaton, isFinal and nQ can be retreived from spot tool manually.

        nQ = 2
        def automaton(q, q_, b1, b2, b3, b4, b5):
            return Or(
                    And(q == 0, q_==1, Not(And(b1 <= C , b2 <=C , b3 <=C , b4 <=C , b5 <=C , b1 >= 0.0 , b2 >= 0.0 , b3 >= 0.0 , b4 >= 0.0 , b5 >= 0.0))),
                    And(q == 0, q_==0, And(b1 <= C , b2 <=C , b3 <=C , b4 <=C , b5 <=C , b1 >= 0.0 , b2 >= 0.0 , b3 >= 0.0 , b4 >= 0.0 , b5 >= 0.0)),
                    And(q == 1, q_==1),
                    )
        # Denotes which states in the UCW are final states i.e, those states that should be visited finitely often for every run
        def isFinal(p):
            return p == 1
        
        # This is dummy and not used in the product fixpoint engine; will be removed in future versions.
        def guarantee(q):
            return True
        
        buchi_fixedpoint([stepmother], cinderella, guarantee, 0, automaton, isFinal, nQ, game_type, init)
        
    else:
        if spec_type == "product-co-buchi":

            raise NotImplementedError("Product Co-Buchi fixpoint not implemented for this benchmark.")
            nQ = 2
            def automaton(q, q_, b1, b2, b3, b4, b5):
                return Or(
                        And(q == 0, q_==1, Not(And(b1 <= C , b2 <=C , b3 <=C , b4 <=C , b5 <=C , b1 >= 0.0 , b2 >= 0.0 , b3 >= 0.0 , b4 >= 0.0 , b5 >= 0.0))),
                        And(q == 0, q_==0, And(b1 <= C , b2 <=C , b3 <=C , b4 <=C , b5 <=C , b1 >= 0.0 , b2 >= 0.0 , b3 >= 0.0 , b4 >= 0.0 , b5 >= 0.0)),
                        And(q == 1, q_==1),
                        )
            # Denotes which states in the UCW are final states i.e, those states that should be visited finitely often for every run
            def isFinal(p):
                return p == 1
            
            # This is dummy and not used in the product fixpoint engine; will be removed in future versions.
            def guarantee(q):
                return True
        
            cobuchi_fixedpoint([stepmother], cinderella, guarantee, 0, automaton, isFinal, nQ, game_type, init)

        else:
            if spec_type == "otf":

                raise NotImplementedError("On-the-fly fixpoint not implemented for this benchmark.")
                # Only Buchi Automatons used in this section (i.e., from the negation of the specification)
                # Deterministic Buchi Automatons can be used in this setting as well. 

                nQ = 2
                def automaton(q, q_, b1, b2, b3, b4, b5):
                    return Or(
                            And(q == 0, q_==1, Not(And(b1 <= C , b2 <=C , b3 <=C , b4 <=C , b5 <=C , b1 >= 0.0 , b2 >= 0.0 , b3 >= 0.0 , b4 >= 0.0 , b5 >= 0.0))),
                            And(q == 0, q_==0, And(b1 <= C , b2 <=C , b3 <=C , b4 <=C , b5 <=C , b1 >= 0.0 , b2 >= 0.0 , b3 >= 0.0 , b4 >= 0.0 , b5 >= 0.0)),
                            And(q == 1, q_==1),
                            )
                # Denotes which states in the UCW are final states i.e, those states that should be visited finitely often for every run
                def isFinal(p):
                    return If(p==0, 1, 0)

                #Partition of predicates obtained by finding all combinations of predicates present in the automaton (manual).
                def sigma(b1, b2, b3, b4, b5):
                    return [Not(And(b1 <= C , b2 <=C , b3 <=C , b4 <=C , b5 <=C , b1 >= 0.0 , b2 >= 0.0 , b3 >= 0.0 , b4 >= 0.0 , b5 >= 0.0)), And(b1 <= C , b2 <=C , b3 <=C , b4 <=C , b5 <=C , b1 >= 0.0 , b2 >= 0.0 , b3 >= 0.0 , b4 >= 0.0 , b5 >= 0.0)]

                # This is dummy and not used in the product fixpoint engine; will be removed in future versions.
                def guarantee(b1, b2, b3, b4, b5):
                    return And(True)

                # Call the fixpoint engine for omega regular specifications (k = 3).
                for i in range(0, 4):
                    # otfd_fixedpoint([stepmother], cinderella, guarantee, int(mode), automaton, isFinal, sigma, nQ, i, game_type, init)
                    otfd_fixedpoint_nonsigma([stepmother], cinderella, guarantee, 0, automaton, isFinal, sigma, nQ, i, game_type, init)

            else:
                print("Not a valid input: Please enter \"simple\", \"product-buchi\", \"product-co-buchi\", or \"bounded\" as the third argument")