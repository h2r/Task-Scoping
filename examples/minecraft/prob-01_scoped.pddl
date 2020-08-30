(define (problem MINECRAFTCONTRIVED-1)
(:domain minecraft-contrived)
(:objects
	steve - agent
    apple0 - apple
)
(:init
        (= (agent-x steve) 0)
        (= (agent-y steve) 0)
        (= (agent-z steve) 0)
        ( agent-has-pickaxe steve )
        (= (agent-num-apples steve) 0)
        (= (agent-num-potatoes steve) 0)
        (= (agent-num-orchids steve) 0)
        (= (agent-num-daisies steve) 0)
        (= (agent-num-raw-rabbits steve) 0)
        (= (agent-num-cooked-rabbits steve) 0)
        (= (apple-x apple0) 0)
        (= (apple-y apple0) 1)
        (= (apple-z apple0) 0)
        ( apple-present apple0 )
)
(:goal (and
        (= (agent-num-apples steve) 1)
    )
)
)