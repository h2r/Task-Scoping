(define (domain minecraft-contrived)
(:requirements :typing :fluents :negative-preconditions :universal-preconditions :existential-preconditions)

(:types 
	locatable - object
	agent item block - locatable
	bedrock destructible-block - block
	wooden-block wool-block - destructible-block
	destructible-item diamond stick diamond-axe white-dye blue-dye red-dye - item
	orchid-flower daisy-flower red-tulip - destructible-item
)

(:predicates
	 (present ?i - item)
	 (block-present ?b - block)
	 (agent-alive ?ag - agent)
)

(:functions
	(agent-num-diamond ?ag - agent)
	(agent-num-stick ?ag - agent)
	(agent-num-diamond-axe ?ag - agent)
	(agent-num-white-dye ?ag - agent)
	(agent-num-blue-dye ?ag - agent)
	(agent-num-red-dye ?ag - agent)
	(agent-num-orchid-flower ?ag - agent)
	(agent-num-daisy-flower ?ag - agent)
	(agent-num-red-tulip ?ag - agent)
	(item-hits ?it - destructible-item)
	(agent-num-wooden-block ?ag - agent)
	(agent-num-wool-block ?ag - agent)
	(block-hits ?b - destructible-block)
	(color ?woolb - wool-block)
	(x ?l - locatable)
	(y ?l - locatable)
	(z ?l - locatable)
)

(:action move-north
 :parameters (?ag - agent)
            :precondition (and (agent-alive ?ag)
                         (not (exists (?bl - block) (and (block-present ?bl) 
                                                         (= (x ?bl) (x ?ag))
                                                         (= (y ?bl) (+ (y ?ag) 1))
                                                         (= (z ?bl) (z ?ag)))))) 
            :effect (and (increase (y ?ag) 1))
)
                        
(:action move-south 
:parameters (?ag - agent) 
:precondition (and (agent-alive ?ag)
                    (not (exists (?bl - block) (and (block-present ?bl)
                                                    (= (x ?bl) (x ?ag))
                                                    (= (y ?bl) (- (y ?ag) 1))
                                                    (= (z ?bl) (z ?ag)))))) 
:effect (and (decrease (y ?ag) 1))
)
            
(:action move-east
    :parameters (?ag - agent)
    :precondition (and (agent-alive ?ag)
                        (not (exists (?bl - block) (and (block-present ?bl)
                                                        (= (x ?bl) (+ (x ?ag) 1))
                                                        (= (y ?bl) (y ?ag))
                                                        (= (z ?bl) (z ?ag)))))) 
    :effect (and (increase (x ?ag) 1))
    )
             
(:action move-west
    :parameters (?ag - agent)
    :precondition (and (agent-alive ?ag)
                    (not (exists (?bl - block) (and (block-present ?bl)
                                                    (= (x ?bl) (- (x ?ag) 1))
                                                    (= (y ?bl) (y ?ag))
                                                    (= (z ?bl) (z ?ag))))))
    :effect (and (decrease (x ?ag) 1))
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


(:action pickup-diamond-axe
 :parameters (?ag - agent ?i - diamond-axe)
 :precondition (and (present ?i)
                    (= (x ?i) (x ?ag))
                    (= (y ?i) (y ?ag))
                    (= (z ?i) (z ?ag)))
 :effect (and (increase (agent-num-diamond-axe ?ag) 1)
              (not (present ?i)))
)


(:action pickup-white-dye
 :parameters (?ag - agent ?i - white-dye)
 :precondition (and (present ?i)
                    (= (x ?i) (x ?ag))
                    (= (y ?i) (y ?ag))
                    (= (z ?i) (z ?ag)))
 :effect (and (increase (agent-num-white-dye ?ag) 1)
              (not (present ?i)))
)


(:action pickup-blue-dye
 :parameters (?ag - agent ?i - blue-dye)
 :precondition (and (present ?i)
                    (= (x ?i) (x ?ag))
                    (= (y ?i) (y ?ag))
                    (= (z ?i) (z ?ag)))
 :effect (and (increase (agent-num-blue-dye ?ag) 1)
              (not (present ?i)))
)


(:action pickup-red-dye
 :parameters (?ag - agent ?i - red-dye)
 :precondition (and (present ?i)
                    (= (x ?i) (x ?ag))
                    (= (y ?i) (y ?ag))
                    (= (z ?i) (z ?ag)))
 :effect (and (increase (agent-num-red-dye ?ag) 1)
              (not (present ?i)))
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


(:action drop-white-dye
 :parameters (?ag - agent ?i - white-dye)
 :precondition (and (>= (agent-num-white-dye ?ag) 1)
                    (not (present ?i)))
 :effect (and (present ?i)
              (assign (x ?i) (x ?ag))
              (assign (y ?i) (+ (y ?ag) 1))
              (assign (z ?i) (z ?ag))
              (decrease (agent-num-white-dye ?ag) 1)
         )
)


(:action drop-blue-dye
 :parameters (?ag - agent ?i - blue-dye)
 :precondition (and (>= (agent-num-blue-dye ?ag) 1)
                    (not (present ?i)))
 :effect (and (present ?i)
              (assign (x ?i) (x ?ag))
              (assign (y ?i) (+ (y ?ag) 1))
              (assign (z ?i) (z ?ag))
              (decrease (agent-num-blue-dye ?ag) 1)
         )
)


(:action drop-red-dye
 :parameters (?ag - agent ?i - red-dye)
 :precondition (and (>= (agent-num-red-dye ?ag) 1)
                    (not (present ?i)))
 :effect (and (present ?i)
              (assign (x ?i) (x ?ag))
              (assign (y ?i) (+ (y ?ag) 1))
              (assign (z ?i) (z ?ag))
              (decrease (agent-num-red-dye ?ag) 1)
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


(:action apply-white-dye
 :parameters (?ag - agent ?woolb - wool-block)
 :precondition (and (not (block-present ?woolb)) (>= (agent-num-wool-block ?ag) 1) (>= (agent-num-white-dye ?ag) 1))
 :effect (and (decrease (agent-num-white-dye ?ag) 1) (assign (color ?woolb) 0)))

(:action apply-blue-dye
 :parameters (?ag - agent ?woolb - wool-block)
 :precondition (and (not (block-present ?woolb)) (>= (agent-num-wool-block ?ag) 1) (>= (agent-num-blue-dye ?ag) 1))
 :effect (and (decrease (agent-num-blue-dye ?ag) 1) (assign (color ?woolb) 1)))

(:action apply-red-dye
 :parameters (?ag - agent ?woolb - wool-block)
 :precondition (and (not (block-present ?woolb)) (>= (agent-num-wool-block ?ag) 1) (>= (agent-num-red-dye ?ag) 1))
 :effect (and (decrease (agent-num-red-dye ?ag) 1) (assign (color ?woolb) 2)))



(:action craft-diamond-axe
    :parameters ( ?ag - agent )
    :precondition ( and
                      ( >= (agent-num-stick ?ag) 2 )
                      ( >= (agent-num-diamond ?ag) 3 )
                  )
    :effect (and (increase (agent-num-diamond-axe ?ag) 1)
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
                        (= (z ?b) (z ?ag))
                        (block-present ?b)
                        (< (block-hits ?b) 2)
                        ( >= ( agent-num-diamond-axe ?ag ) 1 ))
    :effect (and (increase (block-hits ?b) 1))
    )

(:action destroy-wooden-block
    :parameters (?ag - agent ?b - wooden-block)
    :precondition (and (= (x ?b) (x ?ag))
                        (= (y ?b) (+ (y ?ag) 1))
                        (= (z ?b) (z ?ag))
                        (block-present ?b)
                        (= (block-hits ?b) 2)
                        ( >= ( agent-num-diamond-axe ?ag ) 1 ))
    :effect (and (not (block-present ?b))
                 (increase (agent-num-wooden-block ?ag) 1)
            )
    )

(:action hit-wool-block
    :parameters (?ag - agent ?b - wool-block)
    :precondition (and (= (x ?b) (x ?ag))
                        (= (y ?b) (+ (y ?ag) 1))
                        (= (z ?b) (z ?ag))
                        (block-present ?b)
                        (< (block-hits ?b) 2)
                        ( >= ( agent-num-diamond-axe ?ag ) 1 ))
    :effect (and (increase (block-hits ?b) 1))
    )

(:action destroy-wool-block
    :parameters (?ag - agent ?b - wool-block)
    :precondition (and (= (x ?b) (x ?ag))
                        (= (y ?b) (+ (y ?ag) 1))
                        (= (z ?b) (z ?ag))
                        (block-present ?b)
                        (= (block-hits ?b) 2)
                        ( >= ( agent-num-diamond-axe ?ag ) 1 ))
    :effect (and (not (block-present ?b))
                 (increase (agent-num-wool-block ?ag) 1)
            )
    )

(:action destroy-orchid-flower
    :parameters (?ag - agent ?b - orchid-flower)
    :precondition (and (= (x ?b) (x ?ag))
                        (= (y ?b) (+ (y ?ag) 1))
                        (= (z ?b) (z ?ag))
                        (present ?b)
                        (= (item-hits ?b) 0)
                        ( >= ( agent-num-diamond-axe ?ag ) 1 ))
    :effect (and (not (present ?b))
                 (increase (agent-num-orchid-flower ?ag) 1)
            )
    )

(:action destroy-daisy-flower
    :parameters (?ag - agent ?b - daisy-flower)
    :precondition (and (= (x ?b) (x ?ag))
                        (= (y ?b) (+ (y ?ag) 1))
                        (= (z ?b) (z ?ag))
                        (present ?b)
                        (= (item-hits ?b) 0)
                        ( >= ( agent-num-diamond-axe ?ag ) 1 ))
    :effect (and (not (present ?b))
                 (increase (agent-num-daisy-flower ?ag) 1)
            )
    )

(:action destroy-red-tulip
    :parameters (?ag - agent ?b - red-tulip)
    :precondition (and (= (x ?b) (x ?ag))
                        (= (y ?b) (+ (y ?ag) 1))
                        (= (z ?b) (z ?ag))
                        (present ?b)
                        (= (item-hits ?b) 0)
                        ( >= ( agent-num-diamond-axe ?ag ) 1 ))
    :effect (and (not (present ?b))
                 (increase (agent-num-red-tulip ?ag) 1)
            )
    )

)