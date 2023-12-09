; pickup key -> unlock door -> open door

(define (domain pickup-unlock-open)
(:requirements :equality :typing :fluents :negative-preconditions)

(:types 
    door - object
)

(:predicates
    (has-key ?d - door)
    (is-unlocked ?d - door)
    (is-open ?d - door)
)


(:action pickup-key
 :parameters (?d - door)
            :precondition (not (has-key ?d))
            :effect (has-key ?d)
)


(:action unlock-door
 :parameters (?d - door)
            :precondition (and (has-key ?d) (not (is-unlocked ?d)) )
            :effect (is-unlocked ?d)
)           

(:action open-door
 :parameters (?d - door)
            :precondition (and (is-unlocked ?d) (not (is-open ?d)) )
            :effect (is-open ?d)
)  
)