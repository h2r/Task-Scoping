;; Domain constructed by: Nishanth J. Kumar (nkumar12@cs.brown.edu)

(:requirements :typing :fluents :negative-preconditions :universal-preconditions)

(:types agent 
        glass-block 
        apple 
        potato 
        rabbit 
        diamond-axe 
        orchid-flower 
        dirt-block 
        daisy-flower 
        redstone-block 
        lava - object)

(:predicates (gb-present ?gb - glass-block)
             (db-present ?db - dirt-block)
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

            (gb-x ?gb - glass-block)
            (gb-y ?gb - glass-block)
            (gb-z ?gb - glass-block)
            (gb-hits ?gb - glass-block)

            (db-x ?db - dirt-block)  
            (db-y ?db - dirt-block)
            (db-z ?db - dirt-block)
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

(:action move-north
 :parameters (?ag - agent)
 :precondition (and (agent-alive(?ag)
                    ()))
)