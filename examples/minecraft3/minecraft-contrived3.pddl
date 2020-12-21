(define (domain minecraft-contrived)
(:requirements :typing :fluents :negative-preconditions :universal-preconditions :existential-preconditions)

(:types 
	locatable - object
	agent item block - locatable
	bedrock destructible-block - block
	wooden-block wool-block - destructible-block
	destructible-item diamond stick diamond-pickaxe apple potato rabbit - item
	orchid-flower daisy-flower red-tulip - destructible-item
)

(:predicates
	 (present ?i - item)
	 (block-present ?b - block)
	 (agent-alive ?ag - agent)
)

(:functions
	(agent-num-destructible-item ?ag - agent)
	(agent-num-diamond ?ag - agent)
	(agent-num-stick ?ag - agent)
	(agent-num-diamond-pickaxe ?ag - agent)
	(agent-num-apple ?ag - agent)
	(agent-num-potato ?ag - agent)
	(agent-num-rabbit ?ag - agent)
	(block-hits ?b - destructible-block)
	(agent-num-wooden-block ?ag - agent)
	(agent-num-wool-block ?ag - agent)
	(x ?l - locatable)
	(y ?l - locatable)
	(z ?l - locatable)
)

(:action move-north
 :parameters (?ag - agent)
 :precondition (and (agent-alive ?ag)
                    (not (exists (?bl - block) (and (= (x ?bl) (x ?ag))
                                                    (= (y ?bl) (+ (y ?ag) 1))
                                                    (= (z ?bl) (+ (z ?ag) 1))))))
 :effect (and (increase (y ?ag) 1))
)

(:action move-south
 :parameters (?ag - agent)
 :precondition (and (agent-alive ?ag)
                    (not (exists (?bl - block) (and (= (x ?bl) (x ?ag))
                                                    (= (y ?bl) (- (y ?ag) 1))
                                                    (= (z ?bl) (+ (z ?ag) 1))))))
 :effect (and (decrease (y ?ag) 1))
)

(:action move-east
 :parameters (?ag - agent)
 :precondition (and (agent-alive ?ag)
                    (not (exists (?bl - block) (and (= (x ?bl) (+ (x ?ag) 1))
                                                    (= (y ?bl) (y ?ag))
                                                    (= (z ?bl) (+ (z ?ag) 1))))))
 :effect (and (increase (x ?ag) 1))
)

(:action move-west
 :parameters (?ag - agent)
 :precondition (and (agent-alive ?ag)
                    (not (exists (?bl - block) (and (= (x ?bl) (- (x ?ag) 1))
                                                    (= (y ?bl) (y ?ag))
                                                    (= (z ?bl) (+ (z ?ag) 1))))))
 :effect (and (decrease (x ?ag) 1))
)

(:action pickup-destructible-item
 :parameters (?ag - agent ?i - destructible-item)
 :precondition (and (present ?i)
                    (= (x ?i) (x ?ag))
                    (= (y ?i) (y ?ag))
                    (= (z ?i) (z ?ag)))
 :effect (and (increase (agent-num-destructible-item ?ag) 1)
              (not (present ?i)))
)


(:action pickup-diamond
 :parameters (?ag - agent ?i - diamond)
 :precondition (and (present ?i)
                    (= (x ?i) (x ?ag))
                    (= (y ?i) (y ?ag))
                    (= (z ?i) (z ?ag)))
 :effect (and (increase (agent-num-diamond ?ag) 1)
              (not (present ?i)))
)


(:action pickup-stick
 :parameters (?ag - agent ?i - stick)
 :precondition (and (present ?i)
                    (= (x ?i) (x ?ag))
                    (= (y ?i) (y ?ag))
                    (= (z ?i) (z ?ag)))
 :effect (and (increase (agent-num-stick ?ag) 1)
              (not (present ?i)))
)


(:action pickup-diamond-pickaxe
 :parameters (?ag - agent ?i - diamond-pickaxe)
 :precondition (and (present ?i)
                    (= (x ?i) (x ?ag))
                    (= (y ?i) (y ?ag))
                    (= (z ?i) (z ?ag)))
 :effect (and (increase (agent-num-diamond-pickaxe ?ag) 1)
              (not (present ?i)))
)


(:action pickup-apple
 :parameters (?ag - agent ?i - apple)
 :precondition (and (present ?i)
                    (= (x ?i) (x ?ag))
                    (= (y ?i) (y ?ag))
                    (= (z ?i) (z ?ag)))
 :effect (and (increase (agent-num-apple ?ag) 1)
              (not (present ?i)))
)


(:action pickup-potato
 :parameters (?ag - agent ?i - potato)
 :precondition (and (present ?i)
                    (= (x ?i) (x ?ag))
                    (= (y ?i) (y ?ag))
                    (= (z ?i) (z ?ag)))
 :effect (and (increase (agent-num-potato ?ag) 1)
              (not (present ?i)))
)


(:action pickup-rabbit
 :parameters (?ag - agent ?i - rabbit)
 :precondition (and (present ?i)
                    (= (x ?i) (x ?ag))
                    (= (y ?i) (y ?ag))
                    (= (z ?i) (z ?ag)))
 :effect (and (increase (agent-num-rabbit ?ag) 1)
              (not (present ?i)))
)


(:action drop-destructible-item
 :parameters (?ag - agent ?i - destructible-item)
 :precondition (and (>= (agent-num-destructible-item ?ag) 1)
                    (not (present ?i)))
 :effect (and (present ?i)
              (assign (x ?i) (x ?ag))
              (assign (y ?i) (+ (y ?ag) 1))
              (assign (z ?i) (z ?ag))
              (decrease (agent-num-destructible-item ?ag) 1)
         )
)


(:action drop-diamond
 :parameters (?ag - agent ?i - diamond)
 :precondition (and (>= (agent-num-diamond ?ag) 1)
                    (not (present ?i)))
 :effect (and (present ?i)
              (assign (x ?i) (x ?ag))
              (assign (y ?i) (+ (y ?ag) 1))
              (assign (z ?i) (z ?ag))
              (decrease (agent-num-diamond ?ag) 1)
         )
)


(:action drop-stick
 :parameters (?ag - agent ?i - stick)
 :precondition (and (>= (agent-num-stick ?ag) 1)
                    (not (present ?i)))
 :effect (and (present ?i)
              (assign (x ?i) (x ?ag))
              (assign (y ?i) (+ (y ?ag) 1))
              (assign (z ?i) (z ?ag))
              (decrease (agent-num-stick ?ag) 1)
         )
)


(:action drop-apple
 :parameters (?ag - agent ?i - apple)
 :precondition (and (>= (agent-num-apple ?ag) 1)
                    (not (present ?i)))
 :effect (and (present ?i)
              (assign (x ?i) (x ?ag))
              (assign (y ?i) (+ (y ?ag) 1))
              (assign (z ?i) (z ?ag))
              (decrease (agent-num-apple ?ag) 1)
         )
)


(:action drop-potato
 :parameters (?ag - agent ?i - potato)
 :precondition (and (>= (agent-num-potato ?ag) 1)
                    (not (present ?i)))
 :effect (and (present ?i)
              (assign (x ?i) (x ?ag))
              (assign (y ?i) (+ (y ?ag) 1))
              (assign (z ?i) (z ?ag))
              (decrease (agent-num-potato ?ag) 1)
         )
)


(:action drop-rabbit
 :parameters (?ag - agent ?i - rabbit)
 :precondition (and (>= (agent-num-rabbit ?ag) 1)
                    (not (present ?i)))
 :effect (and (present ?i)
              (assign (x ?i) (x ?ag))
              (assign (y ?i) (+ (y ?ag) 1))
              (assign (z ?i) (z ?ag))
              (decrease (agent-num-rabbit ?ag) 1)
         )
)


(:action drop-wooden-block
 :parameters (?ag - agent ?b - wooden-block)
 :precondition (and (>= (agent-num-wooden-block ?ag) 1)
                    (not (block-present ?b)))
 :effect (and (block-present ?b)
              (assign (x ?b) (x ?ag))
              (assign (y ?b) (+ (y ?ag) 1))
              (assign (z ?b) (z ?ag))
              (decrease (agent-num-wooden-block ?ag) 1)
         )
)


(:action drop-wool-block
 :parameters (?ag - agent ?b - wool-block)
 :precondition (and (>= (agent-num-wool-block ?ag) 1)
                    (not (block-present ?b)))
 :effect (and (block-present ?b)
              (assign (x ?b) (x ?ag))
              (assign (y ?b) (+ (y ?ag) 1))
              (assign (z ?b) (z ?ag))
              (decrease (agent-num-wool-block ?ag) 1)
         )
)


(:action craft-diamond-pickaxe
    :parameters ( ?ag - agent )
    :precondition ( and
                      ( >= (agent-num-stick ?ag) 2 )
                      ( >= (agent-num-diamond ?ag) 3 )
                  )
    :effect (and (increase (agent-num-diamond-pickaxe ?ag) 1)
        (decrease (agent-num-stick ?ag) 2)
        (decrease (agent-num-diamond ?ag) 3))

)

(:action craft-red-dye
    :parameters ( ?ag - agent )
    :precondition ( and
                      ( >= (agent-num-red-tulip ?ag) 1 )
                  )
    :effect (and (increase (agent-num-red-dye ?ag) 1)
        (decrease (agent-num-red-tulip ?ag) 1))

)

(:action craft-blue-dye
    :parameters ( ?ag - agent )
    :precondition ( and
                      ( >= (agent-num-orchid-flower ?ag) 1 )
                  )
    :effect (and (increase (agent-num-blue-dye ?ag) 1)
        (decrease (agent-num-orchid-flower ?ag) 1))

)

(:action craft-white-dye
    :parameters ( ?ag - agent )
    :precondition ( and
                      ( >= (agent-num-daisy-flower ?ag) 1 )
                  )
    :effect (and (increase (agent-num-white-dye ?ag) 1)
        (decrease (agent-num-daisy-flower ?ag) 1))

)

(:action hit-wooden-block
    :parameters (?ag - agent ?b - wooden-block)
    :precondition (and (= (x ?b) (x ?ag))
                        (= (y ?b) (+ (y ?ag) 1))
                        (= (z ?b) (+ (z ?ag) 1))
                        (block-present ?b)
                        (< (block-hits ?b) 4)
                        ( >= ( agent-num-diamond-pickaxe ?ag ) 1 ))
    :effect (and (increase (block-hits ?b) 1))
    )

(:action destroy-wooden-block
    :parameters (?ag - agent ?b - wooden-block)
    :precondition (and (= (x ?b) (x ?ag))
                        (= (y ?b) (+ (y ?ag) 1))
                        (= (z ?b) (+ (z ?ag) 1))
                        (block-present ?b)
                        (= (block-hits ?b) 3)
                        ( >= ( agent-num-diamond-pickaxe ?ag ) 1 ))
    :effect (and (not (block-present ?b))
                 (increase (agent-num-wooden-block ?ag) 1)
            )
    )

(:action hit-wool-block
    :parameters (?ag - agent ?b - wool-block)
    :precondition (and (= (x ?b) (x ?ag))
                        (= (y ?b) (+ (y ?ag) 1))
                        (= (z ?b) (+ (z ?ag) 1))
                        (block-present ?b)
                        (< (block-hits ?b) 4)
                        ( >= ( agent-num-diamond-pickaxe ?ag ) 1 ))
    :effect (and (increase (block-hits ?b) 1))
    )

(:action destroy-wool-block
    :parameters (?ag - agent ?b - wool-block)
    :precondition (and (= (x ?b) (x ?ag))
                        (= (y ?b) (+ (y ?ag) 1))
                        (= (z ?b) (+ (z ?ag) 1))
                        (block-present ?b)
                        (= (block-hits ?b) 3)
                        ( >= ( agent-num-diamond-pickaxe ?ag ) 1 ))
    :effect (and (not (block-present ?b))
                 (increase (agent-num-wool-block ?ag) 1)
            )
    )

(:action destroy-wool-block
    :parameters (?ag - agent ?b - wool-block)
    :precondition (and (= (x ?b) (x ?ag))
                        (= (y ?b) (+ (y ?ag) 1))
                        (= (z ?b) (+ (z ?ag) 1))
                        (present ?b)
                        (= (item-hits ?b) 0)
                        ( >= ( agent-num-diamond-pickaxe ?ag ) 1 ))
    :effect (and (not (present ?b))
                 (increase (agent-num-wool-block ?ag) 1)
            )
    )

(:action destroy-wool-block
    :parameters (?ag - agent ?b - wool-block)
    :precondition (and (= (x ?b) (x ?ag))
                        (= (y ?b) (+ (y ?ag) 1))
                        (= (z ?b) (+ (z ?ag) 1))
                        (present ?b)
                        (= (item-hits ?b) 0)
                        ( >= ( agent-num-diamond-pickaxe ?ag ) 1 ))
    :effect (and (not (present ?b))
                 (increase (agent-num-wool-block ?ag) 1)
            )
    )

(:action destroy-wool-block
    :parameters (?ag - agent ?b - wool-block)
    :precondition (and (= (x ?b) (x ?ag))
                        (= (y ?b) (+ (y ?ag) 1))
                        (= (z ?b) (+ (z ?ag) 1))
                        (present ?b)
                        (= (item-hits ?b) 0)
                        ( >= ( agent-num-diamond-pickaxe ?ag ) 1 ))
    :effect (and (not (present ?b))
                 (increase (agent-num-wool-block ?ag) 1)
            )
    )

)