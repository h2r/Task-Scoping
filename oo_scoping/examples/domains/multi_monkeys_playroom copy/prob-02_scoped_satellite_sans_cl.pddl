(define (problem MULTIMONKEY-02)
(:domain multi_monkeys_playroom)
(:objects
	jack - monkey
    bell1 - bell
    ball1 - ball
    eye1 - eye
    hand1 - hand
    marker1 - marker
;	rb1 rb2 - redbutton
;	gb1 gb2 - greenbutton
;	ls1 ls2 - lightswitch
)
(:init
    (= (eye-x eye1) 0)
    (= (eye-y eye1) 0)

    (= (hand-x hand1) 0)
    (= (hand-y hand1) 0)

    (= (marker-x marker1) 0)
    (= (marker-y marker1) 0)

;    (= (lightswitch-x ls1) 2)
;    (= (lightswitch-y ls1) 2)
;    (light-on ls1)
;    (= (lightswitch-x ls2) 3)
;    (= (lightswitch-y ls2) 2)
;    (light-on ls2)

;    (= (rbutton-x rb1) 3)
;    (= (rbutton-y rb1) 3)
;    (= (gbutton-x gb1) 3)
;    (= (gbutton-y gb1) 4)
;    (not (rbutton-on rb1))
;    (gbutton-on gb1)
;    (not (rbutton-on rb1))
;    (connected-buttons rb1 gb1)
;    (= (rbutton-x rb2) 3)
;    (= (rbutton-y rb2) 5)
;    (= (gbutton-x gb2) 3)
;    (= (gbutton-y gb2) 6)
;    (gbutton-on gb2)
;    (rbutton-on rb2)
;    (connected-buttons rb2 gb2)
;    (not (connected-buttons rb1 gb2))
;    (not (connected-buttons rb2 gb1))

    (= (ball-x ball1) 5)
    (= (ball-y ball1) 5)

    (= (bell-x bell1) 80)
    (= (bell-y bell1) 80)
 
    (not (monkey-screaming jack))
    (monkey-watching-bell jack bell1)

)

(:goal (monkey-screaming jack))

)