(define (problem example-1)

(:domain toy-example)

(:objects steve)

(:init
	(not (= n-food 0))
	(not (= n-sticks 0))
	(not (= n-stone 0))
	(not (hungry steve))
	(not (has-axe steve))
)

(:goal (and
		(not (hungry steve))
		(has-axe steve)
	)
)

)
