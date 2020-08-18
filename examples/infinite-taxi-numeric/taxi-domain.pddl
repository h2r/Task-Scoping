;; Domain constructed by: Nishanth J. Kumar (nkumar12@cs.brown.edu)

(define (domain infinite_multipasstaxi)
(:requirements :typing :fluents :negative-preconditions)
; (:requirements :typing)

(:types passenger taxi - object)
(:predicates (passenger-in-taxi ?p - passenger ?t - taxi) )
(:functions (passenger-y ?p - passenger)
            (passenger-x ?p - passenger)
            (taxi-x ?t - taxi)
            (taxi-y ?t - taxi))


(:action pickup
 :parameters (?p - passenger ?t - taxi)
 :precondition (and (= (passenger-x ?p) (taxi-x ?t)) 
                    (= (passenger-y ?p) (taxi-y ?t))
                    (not (passenger-in-taxi ?p ?t)))
 :effect (and (passenger-in-taxi ?p ?t)))

(:action dropoff
 :parameters (?p - passenger ?t - taxi)
 :precondition (passenger-in-taxi ?p ?t)
 :effect (not (passenger-in-taxi ?p ?t)))

(:action move-north
 :parameters (?t - taxi ?p - passenger)
 :precondition (not (passenger-in-taxi ?p ?t))
 :effect (and (increase (taxi-y ?t) 1)))

(:action move-south
 :parameters (?t - taxi ?p - passenger)
 :precondition (not (passenger-in-taxi ?p ?t))
 :effect (and (decrease (taxi-x ?t) 1)))

(:action move-east
 :parameters (?t - taxi ?p - passenger)
 :precondition (not (passenger-in-taxi ?p ?t))
 :effect (and (increase (taxi-x ?t) 1)))

(:action move-west
 :parameters (?t - taxi ?p - passenger)
 :precondition (not (passenger-in-taxi ?p ?t))
 :effect (and (decrease (taxi-y ?t) 1)))

(:action move-north-pass
 :parameters (?t - taxi ?p - passenger)
 :precondition (passenger-in-taxi ?p ?t)
 :effect (and (increase (taxi-y ?t) 1)
              (increase (passenger-y ?p) 1)))

(:action move-south-pass
 :parameters (?t - taxi ?p - passenger)
 :precondition (passenger-in-taxi ?p ?t)
 :effect (and (decrease (taxi-y ?t) 1)
              (decrease (passenger-y ?p) 1)))

(:action move-east-pass
 :parameters (?t - taxi ?p - passenger)
 :precondition (passenger-in-taxi ?p ?t)
 :effect (and (increase (taxi-x ?t) 1)
              (increase (passenger-x ?p) 1)))

(:action move-west-pass
 :parameters (?t - taxi ?p - passenger)
 :precondition (passenger-in-taxi ?p ?t)
 :effect (and (decrease (taxi-x ?t) 1)
              (decrease (passenger-x ?p) 1)))

)