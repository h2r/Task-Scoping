(define (problem outside-left-open-no-key)
    (:domain double-doors)

    (:objects
        d - door
    )

    (:init
        (not (has-key d))
        (left-side-open d)
        (not (is-inside d))
    )

    (:goal
        (is-inside d)
    )
)
