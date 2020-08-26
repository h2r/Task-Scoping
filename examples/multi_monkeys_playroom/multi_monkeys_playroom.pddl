;; Domain constructed by: Nishanth J. Kumar (nkumar12@cs.brown.edu)

; How does this domain work?
; There are some number of lightswitches, red buttons and green buttons. 
; To interact with any of them, the eye and hand must be over them, and then 
; the relevant interact action must be called.
; All light switches must be turned on in order to interact with either of the 
; buttons
; Red and green buttons are 'connected'. You can only press a red button if the 
; green button is on and vice-versa. When a green button is on, music is played, and 
; turning a red button on turns the music off and also toggles the green button

(define (domain multi_monkeys_playroom)
(:requirements :equality :typing :fluents :negative-preconditions :universal-preconditions :existential-preconditions)

(:types eye hand marker ball bell redbutton greenbutton lightswitch monkey - object)
(:predicates (rbutton-on ?rb - redbutton)
             (gbutton-on ?gb - greenbutton)
             (light-on ?lt - lightswitch)
             (monkey-screaming ?mo - monkey)
             (connected-buttons ?rb - redbutton ?gb - greenbutton))

(:functions (rbutton-x ?rb - redbutton)
            (rbutton-y ?rb - redbutton)

            (gbutton-x ?gb - greenbutton)
            (gbutton-y ?gb - greenbutton)

            (lightswitch-x ?ls - lightswitch)
            (lightswitch-y ?ls - lightswitch)

            (eye-x ?e - eye)
            (eye-y ?e - eye)

            (hand-x ?ha - hand)
            (hand-y ?ha - hand)

            (marker-x ?ma - marker)
            (marker-y ?ma - marker)

            (ball-x ?ba - ball)
            (ball-y ?ba - ball)

            (bell-x ?be - bell)
            (bell-y ?be - bell)

            (monkey-x ?mo - monkey)
            (monkey-y ?mo - monkey)

)

; Movement actions for the eye
(:action move-north-eye
 :parameters (?e - eye)
 :precondition ()
 :effect (and (increase (eye-y ?e) 1))
)
(:action move-south-eye
 :parameters (?e - eye)
 :precondition ()
 :effect (and (decrease (eye-y ?e) 1))
)
(:action move-east-eye
 :parameters (?e - eye)
 :precondition ()
 :effect (and (increase (eye-x ?e) 1))
)
(:action move-west-eye
 :parameters (?e - eye)
 :precondition ()
 :effect (and (decrease (eye-x ?e) 1))
)

; Movement actions for the hand
(:action move-north-hand
 :parameters (?ha - hand)
 :precondition ()
 :effect (and (increase (hand-y ?ha) 1))
)
(:action move-south-hand
 :parameters (?ha - hand)
 :precondition ()
 :effect (and (decrease (hand-y ?ha) 1))
)
(:action move-east-hand
 :parameters (?ha - hand)
 :precondition ()
 :effect (and (increase (hand-x ?ha) 1))
)
(:action move-west-hand
 :parameters (?ha - hand)
 :precondition ()
 :effect (and (decrease (hand-x ?ha) 1))
)

; Movement actions for the marker
(:action move-north-marker
 :parameters (?ma - marker)
 :precondition ()
 :effect (and (increase (marker-y ?ma) 1))
)
(:action move-south-marker
 :parameters (?ma - marker)
 :precondition ()
 :effect (and (decrease (marker-y ?ma) 1))
)
(:action move-east-marker
 :parameters (?ma - marker)
 :precondition ()
 :effect (and (increase (marker-x ?ma) 1))
)
(:action move-west-marker
 :parameters (?ma - marker)
 :precondition ()
 :effect (and (decrease (marker-x ?ma) 1))
)

; Turn on and off lights
(:action turn_on_light
 :parameters (?ls - lightswitch ?ma - marker ?e - eye)
 :precondition (and (= (lightswitch-x ?ls) (marker-x ?ma))
                    (= (lightswitch-y ?ls) (marker-y ?ma))
                    (= (lightswitch-x ?ls) (eye-x ?e))
                    (= (lightswitch-y ?ls) (eye-y ?e))
                    (not (light-on ?ls)))
 :effect (light-on ?ls)
)
(:action turn_off_light
 :parameters (?ls - lightswitch ?ma - marker ?e - eye)
 :precondition (and (= (lightswitch-x ?ls) (marker-x ?ma))
                    (= (lightswitch-y ?ls) (marker-y ?ma))
                    (= (lightswitch-x ?ls) (eye-x ?e))
                    (= (lightswitch-y ?ls) (eye-y ?e))
                    (light-on ?ls))
 :effect (not (light-on ?ls))
)

; Toggle red and green buttons
(:action turn_on_redbutton
 :parameters (?rb - redbutton ?gb - greenbutton ?ma - marker ?e - eye)
 :precondition (and (= (rbutton-x ?rb) (marker-x ?ma))
                    (= (rbutton-y ?rb) (marker-y ?ma))
                    (= (rbutton-x ?rb) (eye-x ?e))
                    (= (rbutton-y ?rb) (eye-y ?e))
                    (connected-buttons ?rb ?gb)
                    (not (gbutton-on ?gb)))
 :effect (and (rbutton-on ?rb)
              (not (gbutton-on ?gb)))
)
(:action turn_on_greenbutton
 :parameters (?rb - redbutton ?gb - greenbutton ?ma - marker ?e - eye)
 :precondition (and (= (gbutton-x ?gb) (marker-x ?ma))
                    (= (gbutton-y ?gb) (marker-y ?ma))
                    (= (gbutton-x ?gb) (eye-x ?e))
                    (= (gbutton-y ?gb) (eye-y ?e))
                    (connected-buttons ?rb ?gb)
                    (not (rbutton-on ?rb)))
 :effect (and (gbutton-on ?gb)
              (not (rbutton-on ?rb)))
)
)