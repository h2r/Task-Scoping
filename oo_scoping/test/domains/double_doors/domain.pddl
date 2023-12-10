; There is a two-sided door (left/right). Exactly one is open at a time. Agent can swap which side is open if they have the key.
; Goal is to be inside. Can enter through either side, as long as it is open.

(define (domain double-doors)
(:requirements :equality :typing :fluents :negative-preconditions)

(:types 
    door - object
)

(:predicates
    (has-key ?d - door)
    (left-side-open ?d - door)
    (is-inside ?d - door)
)


(:action pickup-key
 :parameters (?d - door)
            :precondition (not (has-key ?d))
            :effect (has-key ?d)
)


(:action open-left-side
 :parameters (?d - door)
            :precondition (and (has-key ?d) (not (left-side-open ?d)) )
            :effect (left-side-open ?d)
)           

(:action open-right-side
 :parameters (?d - door)
            :precondition (and (has-key ?d) (left-side-open ?d) )
            :effect (not (left-side-open ?d))
)


(:action enter-left-side
 :parameters (?d - door)
            :precondition (and (left-side-open ?d) (not (is-inside ?d)))
            :effect (is-inside ?d)
)


(:action enter-right-side
 :parameters (?d - door)
            :precondition (and (not (left-side-open ?d)) (not (is-inside ?d)))
            :effect (is-inside ?d)
)
)