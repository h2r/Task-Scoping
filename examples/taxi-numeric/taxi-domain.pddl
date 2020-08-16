;; Nishanth J. Kumar (nkumar12@cs.brown.edu)
(define (domain multipasstaxi)
(:requirements :typing :fluents :negative-preconditions)
; (:requirements :typing)

(:types passenger taxi - object)
(:predicates (passenger-in-taxi ?p - passenger ?t - taxi) )
(:functions (passenger-y ?p - passenger)
            (passenger-x ?p - passenger)
            (taxi-x ?t - taxi)
            (taxi-y ?t - taxi)
            (passenger-count ?t - taxi))


(:action pickup
 :parameters (?p - passenger ?t - taxi)
 :precondition (and (= (passenger-x ?p) (taxi-x ?t)) 
                    (= (passenger-y ?p) (taxi-y ?t))
                    (= (passenger-count ?t) 0)
                    (not (passenger-in-taxi ?p ?t)))
 :effect (and (passenger-in-taxi ?p ?t)
              (assign (passenger-count ?t) 1)))

(:action dropoff
 :parameters (?p - passenger ?t - taxi)
 :precondition (and (passenger-in-taxi ?p ?t)
                    (= (passenger-count ?t) 1))
 :effect (and (not (passenger-in-taxi ?p ?t))
              (assign (passenger-count ?t) 0)))

(:action move-north
 :parameters (?t - taxi)
 :precondition (= (passenger-count ?t) 0)
 :effect (and (increase (taxi-y ?t) 1)))

(:action move-south
 :parameters (?t - taxi)
 :precondition (= (passenger-count ?t) 0)
 :effect (and (decrease (taxi-x ?t) 1)))

(:action move-east
 :parameters (?t - taxi)
 :precondition (= (passenger-count ?t) 0)
 :effect (and (increase (taxi-x ?t) 1)))

(:action move-west
 :parameters (?t - taxi)
 :precondition (= (passenger-count ?t) 0)
 :effect (and (decrease (taxi-y ?t) 1)))

(:action move-north-pass
 :parameters (?t - taxi ?p - passenger)
 :precondition (and (= (passenger-count ?t) 1)
                    (passenger-in-taxi ?p ?t))
 :effect (and (increase (taxi-y ?t) 1)
              (increase (passenger-y ?p) 1)))

(:action move-south-pass
 :parameters (?t - taxi ?p - passenger)
 :precondition (and (= (passenger-count ?t) 1)
                    (passenger-in-taxi ?p ?t))
 :effect (and (decrease (taxi-y ?t) 1)
              (decrease (passenger-y ?p) 1)))

(:action move-east-pass
 :parameters (?t - taxi ?p - passenger)
 :precondition (and (= (passenger-count ?t) 1)
                    (passenger-in-taxi ?p ?t))
 :effect (and (increase (taxi-x ?t) 1)
              (increase (passenger-x ?p) 1)))

(:action move-west-pass
 :parameters (?t - taxi ?p - passenger)
 :precondition (and (= (passenger-count ?t) 1)
                    (passenger-in-taxi ?p ?t))
 :effect (and (decrease (taxi-x ?t) 1)
              (decrease (passenger-x ?p) 1)))

)