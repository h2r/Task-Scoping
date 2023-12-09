(define (problem turn-on-radio-initial)
    (:domain turn-on-radio)

    (:objects
        d - door
        r - radio
    )

    (:init
        (not (is-open d))
        (not (is-on r))
    )

    (:goal
        (is-open d)
    )
)
