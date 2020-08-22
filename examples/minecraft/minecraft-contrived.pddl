;; Domain constructed by: Nishanth J. Kumar (nkumar12@cs.brown.edu)

(:requirements :typing :fluents :negative-preconditions :universal-preconditions :existential-preconditions)

(:types dirt-block redstone-block glass-block - block
        agent 
        apple 
        potato 
        rabbit 
        diamond-axe 
        orchid-flower
        daisy-flower 
        block
        lava - object)

(:predicates (block-present ?b - block)
             (apple-present ?ap - apple)
             (daisy-present ?df - daisy-flower)
             (orchid-present ?or - orchid-flower)
             (potato-present ?po - potato)
             (rabbit-present ?ra - rabbit)
             (rabbit-cooked ?ra - rabbit)
             (agent-alive ?ag - agent)
             (agent-has-pickaxe ?ag - agent)
)

(:functions (agent-x ?ag - agent)
            (agent-y ?ag - agent)
            (agent-z ?ag - agent)
            (agent-num-apples ?ag - agent)
            (agent-num-potatoes ?ag - agent)
            (agent-num-orchids ?ag - agent)
            (agent-num-daisies ?ag - daisy-flower)
            (agent-num-raw-rabbits ?ag - agent)
            (agent-num-cooked-rabbits ?ag - agent)

            (bl-x ?bl - block)
            (bl-y ?bl - block)
            (bl-z ?bl - block)

            (gb-hits ?gb - glass-block)

            (db-hits ?db - dirt-block)

            (apple-x ?ap - apple)
            (apple-y ?ap - apple)
            (apple-z ?ap - apple)

            (daisy-x ?df - daisy-flower)
            (daisy-y ?df - daisy-flower)
            (daisy-z ?df - daisy-flower)

            (rabbit-x ?ra - rabbit)
            (rabbit-y ?ra - rabbit)
            (rabbit-z ?ra - rabbit)
)

; Note: There actually cannot be a block at agent-z, agent-z + 1 or agent-z + 2 for any of the move actions
; Right now, I've only implemented agent-z (haven't done "or" condition yet)
(:action move-north
 :parameters (?ag - agent)
 :precondition (and (agent-alive(?ag)
                    (not (exists (?bl - block) (and (= (bl-x ?bl) (agent-x ?ag))
                                                    (= (bl-y ?bl) (+ (agent-y ?ag) 1))
                                                    (= (bl-z ?bl) (+ (agent-z ?ag) 1)))))))
:effect (increase (agent-y ?ag) 1)
)

(:action move-south
 :parameters (?ag - agent)
 :precondition (and (agent-alive(?ag)
                    (not (exists (?bl - block) (and (= (bl-x ?bl) (agent-x ?ag))
                                                    (= (bl-y ?bl) (- (agent-y ?ag) 1))
                                                    (= (bl-z ?bl) (+ (agent-z ?ag) 1)))))))
:effect (decrease (agent-y ?ag) 1)
)