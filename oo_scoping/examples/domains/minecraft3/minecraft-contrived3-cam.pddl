(define (domain minecraft-bedmaking)
(:requirements :equality :typing :fluents :negative-preconditions :universal-preconditions :existential-preconditions)

(:types
	locatable int - object
	agent item block - locatable
	bedrock destructible-block - block
	wooden-block wooden-planks wool-block bed - destructible-block
	destructible-item diamond stick diamond-axe blue-dye - item
	orchid-flower oak-sapling birch-sapling - destructible-item
    position count color - int
)

(:predicates
	(present ?i - item)
	(block-present ?b - block) ;; block is still present in environment
	(agent-alive ?ag - agent)
    (gt ?x1 - int ?x2 - int) ;; x1 > x2
    (lt ?x1 - int ?x2 - int) ;; x1 < x2
    (eq ?x1 - int ?x2 - int) ;; x1 == x2
    (are-seq ?x1 - int ?x2 - int) ;; true if x1 + 1 = x2 (i.e. they are sequential)
    ;(agent-num-diamond ?ag - agent)
    (agent-has-n-diamonds ?ag - agent ?n - count)
    ;(agent-num-stick ?ag - agent)
    (agent-has-n-sticks ?ag - agent ?n - count)
    ;(agent-num-diamond-axe ?ag - agent)
    (agent-has-n-diamond-axes ?ag - agent ?n - count)
    ;(agent-num-blue-dye ?ag - agent)
    (agent-has-n-blue-dye ?ag - agent ?n - count)
    ;(agent-num-orchid-flower ?ag - agent)
    (agent-has-n-orchid-flowers ?ag - agent ?n - count)
    ;(agent-num-birch-sapling ?ag - agent)
    (agent-has-n-birch-saplings ?ag - agent ?n - count)
    ;(agent-num-oak-sapling ?ag - agent)
    (agent-has-n-oak-saplings ?ag - agent ?n - count)
    ;(agent-num-wooden-block ?ag - agent)
    (agent-has-n-wooden-blocks ?ag - agent ?n - count)
    ;(agent-num-wooden-planks ?ag - agent)
    (agent-has-n-wooden-planks ?ag - agent ?n - count)
    ;(agent-num-wool-block ?ag - agent)
    (agent-has-n-wool-blocks ?ag - agent ?n - count)
    ;(agent-num-bed ?ag - agent)
    (agent-has-n-beds ?ag - agent ?n - count)
    ;(item-hits ?it - destructible-item)
    (item-has-n-hits-remaining ?it - destructible-item ?n - count)
    ;(block-hits ?b - destructible-block)
    (block-has-n-hits-remaining ?b - destructible-block)
    ;(wool-color ?woolb - wool-block)
    (wool-has-color-id ?woolb - wool-block ?c - color)
    ;(bed-color ?bd - bed)
    (bed-has-color-id ?bd - bed-block ?c - color)
    ;(x ?l - locatable)
    (at-x ?l - locatable ?x - position)
    ;(y ?l - locatable)
    (at-y ?l - locatable ?y - position)
    ;(z ?l - locatable)
    (at-z ?l - locatable ?z - position)

)


(:action move-north
    :parameters (?ag - agent ?x - position ?y_start - position ?y_end - position ?z - position)
    :precondition (and
        (agent-alive ?ag)
        (at-x ?ag ?x)
        (at-y ?ag ?y_start)
        (at-z ?ag ?z)
        (are-seq ?y_start ?y_end) ;; values increase from south to north
        (not (exists (?bl - block) (and
            (block-present ?bl)
            ; (= (x ?bl) (x ?ag))
            ; (= (y ?bl) (+ (y ?ag) 1))
            ; (= (z ?bl) (z ?ag))
            (at-x ?bl ?x)
            (at-y ?bl ?y_end)
            (at-z ?bl ?z)
        )))
    )
    :effect (and
        ; (increase (y ?ag) 1)
        (not (at-y ?ag ?y_start))
        (at-y ?ag ?y_end)
    )
)


(:action move-south
    :parameters (?ag - agent ?x - position ?y_start - position ?y_end - position ?z - position)
    :precondition (and
        (agent-alive ?ag)
        (at-x ?ag ?x)
        (at-y ?ag ?y_start)
        (at-z ?ag ?z)
        (are-seq ?y_end ?y_start) ;; values increase from south to north
        (not (exists (?bl - block) (and
            (block-present ?bl)
            ; (= (x ?bl) (x ?ag))
            ; (= (y ?bl) (- (y ?ag) 1))
            ; (= (z ?bl) (z ?ag))
            (at-x ?bl ?x)
            (at-y ?bl ?y_end)
            (at-z ?bl ?z)
        )))
    )
    :effect (and
        ; (decrease (y ?ag) 1)
        (not (at-y ?ag ?y_start))
        (at-y ?ag ?y_end)
    )
)


(:action move-east
    :parameters (?ag - agent ?x_start - position ?x_end - position ?y - position ?z - position)
    :precondition (and
        (agent-alive ?ag)
        (at-x ?ag ?x_start)
        (at-y ?ag ?y)
        (at-z ?ag ?z)
        (are-seq ?x_start ?x_end) ;; values increase from west to east
        (not (exists (?bl - block) (and
            (block-present ?bl)
            ; (= (x ?bl) (+ (x ?ag) 1))
            ; (= (y ?bl) (y ?ag))
            ; (= (z ?bl) (z ?ag))
            (at-x ?bl ?x_end)
            (at-y ?bl ?y)
            (at-z ?bl ?z)
        )))
    )
    :effect (and (increase (x ?ag) 1))
)

(:action move-west
    :parameters (?ag - agent ?x_start - position ?x_end - position ?y - position ?z - position)
    :precondition (and
        (agent-alive ?ag)
        (at-x ?ag ?x_start)
        (at-y ?ag ?y)
        (at-z ?ag ?z)
        (are-seq ?x_end ?x_start) ;; values increase from west to east
        (not (exists (?bl - block) (and
            (block-present ?bl)
            ; (= (x ?bl) (+ (x ?ag) 1))
            ; (= (y ?bl) (y ?ag))
            ; (= (z ?bl) (z ?ag))
            (at-x ?bl ?x_end)
            (at-y ?bl ?y)
            (at-z ?bl ?z)
        )))
    )
    :effect (and (decrease (x ?ag) 1))
)

(:action pickup-diamond
    :parameters (
        ?ag - agent
        ?i - diamond
        ?n_start - count
        ?n_end - count
        ?x - position
        ?y - position
        ?z - position
    )
    :precondition (and
        (present ?i)
        ; (= (x ?i) (x ?ag))
        ; (= (y ?i) (y ?ag))
        ; (= (z ?i) (z ?ag))
        (at-x ?ag ?x)
        (at-x ?i ?x)
        (at-y ?ag ?y)
        (at-y ?i ?y)
        (at-z ?ag ?z)
        (at-z ?i ?z)
        (agent-has-n-diamonds ?ag ?n_start)
        (are-seq ?n_start ?n_end)
    )
    :effect (and
        ; (increase (agent-num-diamond ?ag) 1)
        (not (at-x ?i ?x))
        (not (at-y ?i ?y))
        (not (at-z ?i ?z))
        (not (agent-has-n-diamonds ?ag ?n_start))
        (agent-has-n-diamonds ?ag ?n_end)
        (not (present ?i))
    )
)


(:action pickup-stick
    :parameters (
        ?ag - agent
        ?i - stick
        ?n_start - count
        ?n_end - count
        ?x - position
        ?y - position
        ?z - position
    )
    :precondition (and
        (present ?i)
        ; (= (x ?i) (x ?ag))
        ; (= (y ?i) (y ?ag))
        ; (= (z ?i) (z ?ag))
        (at-x ?ag ?x)
        (at-x ?i ?x)
        (at-y ?ag ?y)
        (at-y ?i ?y)
        (at-z ?ag ?z)
        (at-z ?i ?z)
        (agent-has-n-sticks ?ag ?n_start)
        (are-seq ?n_start ?n_end)
    )
    :effect (and
        ; (increase (agent-num-stick ?ag) 1)
        (not (at-x ?i ?x))
        (not (at-y ?i ?y))
        (not (at-z ?i ?z))
        (not (agent-has-n-sticks ?ag ?n_start))
        (agent-has-n-sticks ?ag ?n_end)
        (not (present ?i))
    )
)


(:action pickup-diamond-axe
    :parameters (
        ?ag - agent
        ?i - diamond-axe
        ?n_start - count
        ?n_end - count
        ?x - position
        ?y - position
        ?z - position
    )
    :precondition (and
        (present ?i)
        ; (= (x ?i) (x ?ag))
        ; (= (y ?i) (y ?ag))
        ; (= (z ?i) (z ?ag))
        (at-x ?ag ?x)
        (at-x ?i ?x)
        (at-y ?ag ?y)
        (at-y ?i ?y)
        (at-z ?ag ?z)
        (at-z ?i ?z)
        (agent-has-n-diamond-axes ?ag ?n_start)
        (are-seq ?n_start ?n_end)
    )
    :effect (and
        ; (increase (agent-num-diamond-axe ?ag) 1)
        (not (at-x ?i ?x))
        (not (at-y ?i ?y))
        (not (at-z ?i ?z))
        (not (agent-has-n-diamond-axes ?ag ?n_start))
        (agent-has-n-diamond-axes ?ag ?n_end)
        (not (present ?i))
    )
)


(:action pickup-blue-dye
    :parameters (
        ?ag - agent
        ?i - blue-dye
        ?n_start - count
        ?n_end - count
        ?x - position
        ?y - position
        ?z - position
    )
    :precondition (and
        (present ?i)
        ; (= (x ?i) (x ?ag))
        ; (= (y ?i) (y ?ag))
        ; (= (z ?i) (z ?ag))
        (at-x ?ag ?x)
        (at-x ?i ?x)
        (at-y ?ag ?y)
        (at-y ?i ?y)
        (at-z ?ag ?z)
        (at-z ?i ?z)
        (agent-has-n-blue-dye ?ag ?n_start)
        (are-seq ?n_start ?n_end)
    )
    :effect (and
        ; (increase (agent-num-blue-dye ?ag) 1)
        (not (at-x ?i ?x))
        (not (at-y ?i ?y))
        (not (at-z ?i ?z))
        (not (agent-has-n-blue-dye ?ag ?n_start))
        (agent-has-n-blue-dye ?ag ?n_end)
        (not (present ?i))
    )
)


(:action drop-diamond
    :parameters (
        ?ag - agent
        ?i - diamond
        ?n_start - count
        ?n_end - count
        ?x - position
        ?y_start - position
        ?y_end - position
        ?x - position
    )
    :precondition (and
        ; (>= (agent-num-diamond ?ag) 1)
        (agent-has-n-diamonds ?ag ?n_start)
        (are-seq ?n_end ?n_start)
        (at-x ?ag ?x)
        (at-y ?ag ?y_start)
        (are-seq ?y_start ?y_end) ;; values increase from south to north
        (at-z ?ag ?z)
        (not (present ?i))
    )
    :effect (and
        (present ?i)
        ; (assign (x ?i) (x ?ag))
        ; (assign (y ?i) (+ (y ?ag) 1))
        ; (assign (z ?i) (z ?ag))
        ; (decrease (agent-num-diamond ?ag) 1)
        (at-x ?i ?x)
        (at-y ?i ?y_end)
        (at-z ?i ?z)
        (not agent-has-n-diamonds ?ag ?n_start)
        (agent-has-n-diamonds ?ag ?n_end)

    )
)


(:action drop-stick
    :parameters (
        ?ag - agent
        ?i - stick
        ?n_start - count
        ?n_end - count
        ?x - position
        ?y_start - position
        ?y_end - position
        ?x - position
    )
    :precondition (and
        ; (>= (agent-num-stick ?ag) 1)
        (agent-has-n-sticks ?ag ?n_start)
        (are-seq ?n_end ?n_start)
        (at-x ?ag ?x)
        (at-y ?ag ?y_start)
        (are-seq ?y_start ?y_end) ;; values increase from south to north
        (at-z ?ag ?z)
        (not (present ?i))
    )
    :effect (and
        (present ?i)
        ; (assign (x ?i) (x ?ag))
        ; (assign (y ?i) (+ (y ?ag) 1))
        ; (assign (z ?i) (z ?ag))
        ; (decrease (agent-num-stick ?ag) 1)
        (at-x ?i ?x)
        (at-y ?i ?y_end)
        (at-z ?i ?z)
        (not agent-has-n-sticks ?ag ?n_start)
        (agent-has-n-sticks ?ag ?n_end)
    )
)


(:action drop-blue-dye
    :parameters (
        ?ag - agent
        ?i - blue-dye
        ?n_start - count
        ?n_end - count
        ?x - position
        ?y_start - position
        ?y_end - position
        ?x - position
    )
    :precondition (and
        ; (>= (agent-num-blue-dye ?ag) 1)
        (agent-has-n-blue-dye ?ag ?n_start)
        (are-seq ?n_end ?n_start)
        (at-x ?ag ?x)
        (at-y ?ag ?y_start)
        (are-seq ?y_start ?y_end) ;; values increase from south to north
        (at-z ?ag ?z)
        (not (present ?i))
    )
    :effect (and
        (present ?i)
        ; (assign (x ?i) (x ?ag))
        ; (assign (y ?i) (+ (y ?ag) 1))
        ; (assign (z ?i) (z ?ag))
        ; (decrease (agent-num-blue-dye ?ag) 1)
        (at-x ?i ?x)
        (at-y ?i ?y_end)
        (at-z ?i ?z)
        (not agent-has-n-blue-dye ?ag ?n_start)
        (agent-has-n-blue-dye ?ag ?n_end)
    )
)


(:action drop-wooden-block
    :parameters (
        ?ag - agent
        ?b - wooden-block
        ?n_start - count
        ?n_end - count
        ?x - position
        ?y_start - position
        ?y_end - position
        ?x - position
    )
    :precondition (and
        ; (>= (agent-num-wooden-block ?ag) 1)
        (agent-has-n-wooden-blocks ?ag ?n_start)
        (are-seq ?n_end ?n_start)
        (at-x ?ag ?x)
        (at-y ?ag ?y_start)
        (are-seq ?y_start ?y_end) ;; values increase from south to north
        (at-z ?ag ?z)
        (not (block-present ?b))
    )
    :effect (and
        (block-present ?b)
        ; (assign (x ?b) (x ?ag))
        ; (assign (y ?b) (+ (y ?ag) 1))
        ; (assign (z ?b) (z ?ag))
        ; (decrease (agent-num-wooden-block ?ag) 1)
        (at-x ?i ?x)
        (at-y ?i ?y_end)
        (at-z ?i ?z)
        (not agent-has-n-wooden-blocks ?ag ?n_start)
        (agent-has-n-wooden-blocks ?ag ?n_end)
    )
)


(:action drop-wooden-planks
    :parameters (
        ?ag - agent
        ?b - wooden-planks
        ?n_start - count
        ?n_end - count
        ?x - position
        ?y_start - position
        ?y_end - position
        ?x - position
    )
    :precondition (and
        ; (>= (agent-num-wooden-planks ?ag) 1)
        (agent-has-n-wooden-planks ?ag ?n_start)
        (are-seq ?n_end ?n_start)
        (at-x ?ag ?x)
        (at-y ?ag ?y_start)
        (are-seq ?y_start ?y_end) ;; values increase from south to north
        (at-z ?ag ?z)
        (not (block-present ?b))
    )
    :effect (and
        (block-present ?b)
        ; (assign (x ?b) (x ?ag))
        ; (assign (y ?b) (+ (y ?ag) 1))
        ; (assign (z ?b) (z ?ag))
        ; (decrease (agent-num-wooden-planks ?ag) 1)
        (at-x ?i ?x)
        (at-y ?i ?y_end)
        (at-z ?i ?z)
        (not agent-has-n-wooden-planks ?ag ?n_start)
        (agent-has-n-wooden-planks ?ag ?n_end)
    )
)


(:action drop-wool-block
    :parameters (
        ?ag - agent
        ?b - wool-block
        ?n_start - count
        ?n_end - count
        ?x - position
        ?y_start - position
        ?y_end - position
        ?x - position
    )
    :precondition (and
        ; (>= (agent-num-wool-block ?ag) 1)
        (agent-has-n-wool-blocks ?ag ?n_start)
        (are-seq ?n_end ?n_start)
        (at-x ?ag ?x)
        (at-y ?ag ?y_start)
        (are-seq ?y_start ?y_end) ;; values increase from south to north
        (at-z ?ag ?z)
        (not (block-present ?b))
    )
    :effect (and
        (block-present ?b)
        ; (assign (x ?b) (x ?ag))
        ; (assign (y ?b) (+ (y ?ag) 1))
        ; (assign (z ?b) (z ?ag))
        ; (decrease (agent-num-wool-block ?ag) 1)
        (at-x ?i ?x)
        (at-y ?i ?y_end)
        (at-z ?i ?z)
        (not agent-has-n-wool-blocks ?ag ?n_start)
        (agent-has-n-wool-blocks ?ag ?n_end)
    )
)


(:action drop-bed
    :parameters (
        ?ag - agent
        ?b - bed
        ?n_start - count
        ?n_end - count
        ?x - position
        ?y_start - position
        ?y_end - position
        ?x - position
    )
    :precondition (and
        ; (>= (agent-num-bed ?ag) 1)
        (agent-has-n-beds ?ag ?n_start)
        (are-seq ?n_end ?n_start)
        (at-x ?ag ?x)
        (at-y ?ag ?y_start)
        (are-seq ?y_start ?y_end) ;; values increase from south to north
        (at-z ?ag ?z)
        (not (block-present ?b))
    )
    :effect (and
        (block-present ?b)
        ; (assign (x ?b) (x ?ag))
        ; (assign (y ?b) (+ (y ?ag) 1))
        ; (assign (z ?b) (z ?ag))
        ; (decrease (agent-num-bed ?ag) 1)
        (at-x ?i ?x)
        (at-y ?i ?y_end)
        (at-z ?i ?z)
        (not agent-has-n-beds ?ag ?n_start)
        (agent-has-n-beds ?ag ?n_end)

    )
)


(:action apply-blue-dye
    :parameters (?ag - agent ?woolb - wool-block)
    :precondition (and
        (not (block-present ?woolb))
        (>= (agent-num-wool-block ?ag) 1)
        (>= (agent-num-blue-dye ?ag) 1)
    )
    :effect (and
        (decrease (agent-num-blue-dye ?ag) 1)
        (assign (wool-color ?woolb) 1)
    )
)


(:action craft-bed-blue-dye
:parameters (?ag - agent ?woolb1 - wool-block ?woolb2 - wool-block ?woolb3 - wool-block ?bd - bed ?n_wool_blocks_start - count ?n_wool_blocks_end - count)
:precondition (and
    (not (block-present ?woolb1))
    (not (block-present ?woolb2))
    (not (block-present ?woolb3))
    (= (wool-color ?woolb1) 1)
    (= (wool-color ?woolb2) 1)
    (= (wool-color ?woolb3) 1)
    (not (= ?woolb1 ?woolb2))
    (not (= ?woolb1 ?woolb3))
    (not (= ?woolb2 ?woolb3))
    (not (block-present ?bd))
    ; (>= (agent-num-wool-block ?ag) 3)
    (exists
        (?n_wool_blocks_minus_one - count ?n_wool_blocks_minus_two - count)
        (and
            (are-seq ?n_wool_blocks_end ?n_wool_blocks_minus_two)
            (are-seq ?n_wool_blocks_minus_two ?n_wool_blocks_minus_one)
            (are-seq ?n_wool_blocks_minus_one ?n_wool_blocks_start)
        )
    )
    (>= (agent-num-wooden-planks ?ag) 3)
    ; (are-three-apart ?x1 ?x4)
)
:effect (and
    (decrease (agent-num-wooden-planks ?ag) 3)
    ; (decrease (agent-num-wool-block ?ag) 3)
    (not agent-has-n-wool-blocks ?ag ?n_wool_blocks_start)
    (agent-has-n-wool-blocks ?ag ?n_wool_blocks_end)
    (increase (agent-num-bed ?ag) 1)
    (assign (bed-color ?bd) 1))
)


(:action craft-diamond-axe
    :parameters ( ?ag - agent )
    :precondition (and
        (>= (agent-num-stick ?ag) 2)
        (>= (agent-num-diamond ?ag) 3)
    )
    :effect (and
        (increase (agent-num-diamond-axe ?ag) 1)
        (decrease (agent-num-stick ?ag) 2)
        (decrease (agent-num-diamond ?ag) 3)
    )
)


(:action craft-wooden-planks
    :parameters (?ag - agent ?wb - wooden-block)
    :precondition (and
        (not (block-present ?wb))
        (>= (agent-num-wooden-block ?ag) 1)
    )
    :effect (and
        (decrease (agent-num-wooden-block ?ag) 1)
        (increase (agent-num-wooden-planks ?ag) 4)
    )
)


(:action craft-blue-dye
    :parameters ( ?ag - agent )
    :precondition ( and
        (>= (agent-num-orchid-flower ?ag) 1)
    )
    :effect (and
        (increase (agent-num-blue-dye ?ag) 1)
        (decrease (agent-num-orchid-flower ?ag) 1)
    )
)


(:action hit-wooden-block
    :parameters (?ag - agent ?b - wooden-block)
    :precondition (and
        (= (x ?b) (x ?ag))
        (= (y ?b) (+ (y ?ag) 1))
        (= (z ?b) (z ?ag))
        (block-present ?b)
        (< (block-hits ?b) 2) ;; flip around so you track n-hits-remaining, same mechanism as drop (zero)
        ( >= ( agent-num-diamond-axe ?ag ) 1) ;; exists a predecessor
    )
    :effect (and (increase (block-hits ?b) 1))
)


(:action destroy-wooden-block
    :parameters (?ag - agent ?b - wooden-block)
    :precondition (and
        (= (x ?b) (x ?ag))
        (= (y ?b) (+ (y ?ag) 1))
        (= (z ?b) (z ?ag))
        (block-present ?b)
        (= (block-hits ?b) 2) ;; does not exist successor for n-hits-remaining (because zero)
        (>= ( agent-num-diamond-axe ?ag ) 1)
    )
    :effect (and
        (not (block-present ?b))
        (increase (agent-num-wooden-block ?ag) 1)
        (assign (block-hits ?b) 0)
    )
)


(:action hit-wooden-planks
    :parameters (?ag - agent ?b - wooden-planks)
    :precondition (and
        (= (x ?b) (x ?ag))
        (= (y ?b) (+ (y ?ag) 1))
        (= (z ?b) (z ?ag))
        (block-present ?b)
        (< (block-hits ?b) 2)
        (>= ( agent-num-diamond-axe ?ag ) 1)
    )
    :effect (and (increase (block-hits ?b) 1))
)


(:action destroy-wooden-planks
    :parameters (?ag - agent ?b - wooden-planks)
    :precondition (and
        (= (x ?b) (x ?ag))
        (= (y ?b) (+ (y ?ag) 1))
        (= (z ?b) (z ?ag))
        (block-present ?b)
        (= (block-hits ?b) 2)
        (>= ( agent-num-diamond-axe ?ag ) 1)
    )
    :effect (and
        (not (block-present ?b))
        (increase (agent-num-wooden-planks ?ag) 1)
        (assign (block-hits ?b) 0)
    )
)


(:action hit-bed
    :parameters (?ag - agent ?b - bed)
    :precondition (and
        (= (x ?b) (x ?ag))
        (= (y ?b) (+ (y ?ag) 1))
        (= (z ?b) (z ?ag))
        (block-present ?b)
        (< (block-hits ?b) 2)
        ( >= ( agent-num-diamond-axe ?ag ) 1)
    )
    :effect (and (increase (block-hits ?b) 1))
)


(:action destroy-bed
    :parameters (?ag - agent ?b - bed)
    :precondition (and
        (= (x ?b) (x ?ag))
        (= (y ?b) (+ (y ?ag) 1))
        (= (z ?b) (z ?ag))
        (block-present ?b)
        (= (block-hits ?b) 2)
        ( >= ( agent-num-diamond-axe ?ag ) 1)
    )
    :effect (and
        (not (block-present ?b))
        (increase (agent-num-bed ?ag) 1)
        (assign (block-hits ?b) 0)
    )
)


(:action destroy-orchid-flower
    :parameters (?ag - agent ?b - orchid-flower)
    :precondition (and
        (= (x ?b) (x ?ag))
        (= (y ?b) (+ (y ?ag) 1))
        (= (z ?b) (z ?ag))
        (present ?b)
        (= (item-hits ?b) 0)
    )
    :effect (and
        (not (present ?b))
        (increase (agent-num-orchid-flower ?ag) 1)
        (assign (item-hits ?b) 0)
    )
)


(:action destroy-oak-sapling
    :parameters (?ag - agent ?b - oak-sapling)
    :precondition (and
        (= (x ?b) (x ?ag))
        (= (y ?b) (+ (y ?ag) 1))
        (= (z ?b) (z ?ag))
        (present ?b)
        (= (item-hits ?b) 0)
    )
    :effect (and
        (not (present ?b))
        (increase (agent-num-oak-sapling ?ag) 1)
        (assign (item-hits ?b) 0)
    )
)


(:action destroy-birch-sapling
    :parameters (?ag - agent ?b - birch-sapling)
    :precondition (and
        (= (x ?b) (x ?ag))
        (= (y ?b) (+ (y ?ag) 1))
        (= (z ?b) (z ?ag))
        (present ?b)
        (= (item-hits ?b) 0)
    )
    :effect (and
        (not (present ?b))
        (increase (agent-num-birch-sapling ?ag) 1)
        (assign (item-hits ?b) 0)
    )
)

)
