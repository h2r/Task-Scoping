; pickup key -> unlock door -> open door

(define (domain turn-on-radio)
(:requirements :equality :typing :fluents :negative-preconditions)

(:types 
    door radio - object
)

(:predicates
    (is-open ?d - door)
    (is-on ?r - radio)
)



(:action open-door
 :parameters (?d - door)
            :precondition (not (is-open ?d))
            :effect (is-open ?d)
)  

(:action turn-on-radio
 :parameters (?r - radio)
            :precondition (not (is-on ?r))
            :effect (is-on ?r)
)  

)