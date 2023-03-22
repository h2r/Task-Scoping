(define (domain toy-example)
(:requirements :equality :fluents)

(:predicates
    (n-food ?n)
    (n-sticks ?n)
    (n-stone ?n)
    (hungry ?ag)
    (has-axe ?ag)
)

(:action get_food
    :parameters (?n)
    :precondition (and (< (n-food ?n) 5))
    :effect (and (increase (n-food ?n)))
)

(:action get_stick
    :parameters (?n)
    :precondition (and (< (n-sticks ?n) 5))
    :effect (and (increase (n-sticks ?n)))
)

(:action get_stone
    :parameters (?n)
    :precondition (and (< (n-stone ?n) 5))
    :effect (and (increase (n-stone ?n)))
)

(:action eat
    :parameters (?n ?ag)
    :precondition (and (> (n-food ?n) 0))
    :effect (and
        (decrease (n-food ?n))
        (not (hungry ?ag))
    )
)

(:action make_axe
    :parameters (?n_sticks ?n_stone ?ag)
    :precondition (and
        (> (n-sticks ?n) 0)
        (> (n-stone ?n) 0)
        (not (has-axe ?ag))
    )
    :effect (and
        (decrease (n-sticks ?n))
        (decrease (n-stone ?n))
        (has-axe ?ag)
    )
)
