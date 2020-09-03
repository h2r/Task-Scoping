(define (domain minecraft-contrived)
(:requirements :typing :fluents :negative-preconditions :universal-preconditions :existential-preconditions)

(:types 
	locatable
	agent item block - locatable
	bedrock destructible-block - block
	obsidian-block - destructible-block
	diamond stick iron diamond-pickaxe shears wool - item
)

(:predicates
	 ( present ?i - item )
	 ( block-present ?b - block )
	 ( agent-alive ?ag - agent )
)

(:functions
	( block-hits ?b - destructible-block )
	( agent-num-diamond ?ag - agent )
	( agent-num-stick ?ag - agent )
	( agent-num-iron ?ag - agent )
	( agent-num-diamond-pickaxe ?ag - agent )
	( agent-num-shears ?ag - agent )
	( agent-num-wool ?ag - agent )
	( x ?l - locatable )
	( y ?l - locatable )
	( z ?l - locatable )
)

(:action move-north
 :parameters (?ag - agent)
 :precondition (and (agent-alive ?ag)
                    (not (exists (?bl - block) (and (= (x ?bl) (x ?ag))
                                                    (= (y ?bl) (+ (y ?ag) 1))
                                                    (= (z ?bl) (+ (z ?ag) 1))))))
 :effect (and (increase (y ?ag) 1))
)

(:action move-south
 :parameters (?ag - agent)
 :precondition (and (agent-alive ?ag)
                    (not (exists (?bl - block) (and (= (x ?bl) (x ?ag))
                                                    (= (y ?bl) (- (y ?ag) 1))
                                                    (= (z ?bl) (+ (z ?ag) 1))))))
 :effect (and (decrease (y ?ag) 1))
)

(:action move-east
 :parameters (?ag - agent)
 :precondition (and (agent-alive ?ag)
                    (not (exists (?bl - block) (and (= (x ?bl) (+ (x ?ag) 1))
                                                    (= (y ?bl) (y ?ag))
                                                    (= (z ?bl) (+ (z ?ag) 1))))))
 :effect (and (increase (x ?ag) 1))
)

(:action move-west
 :parameters (?ag - agent)
 :precondition (and (agent-alive ?ag)
                    (not (exists (?bl - block) (and (= (x ?bl) (- (x ?ag) 1))
                                                    (= (y ?bl) (y ?ag))
                                                    (= (z ?bl) (+ (z ?ag) 1))))))
 :effect (and (decrease (x ?ag) 1))
)

;(:action pickup-diamond
; :parameters (?ag - agent ?i - diamond)
; :precondition (and (present ?i)
;                    (= (x ?i) (x ?ag))
;                    (= (y ?i) (y ?ag))
;                    (= (z ?i) (z ?ag)))
; :effect (and (increase (agent-num-diamond ?ag) 1)
;              (not (present ?i)))
;)


;(:action pickup-stick
; :parameters (?ag - agent ?i - stick)
; :precondition (and (present ?i)
;                    (= (x ?i) (x ?ag))
;                    (= (y ?i) (y ?ag))
;                    (= (z ?i) (z ?ag)))
; :effect (and (increase (agent-num-stick ?ag) 1)
;              (not (present ?i)))
;)


;(:action pickup-iron
; :parameters (?ag - agent ?i - iron)
; :precondition (and (present ?i)
;                    (= (x ?i) (x ?ag))
;                    (= (y ?i) (y ?ag))
;                    (= (z ?i) (z ?ag)))
; :effect (and (increase (agent-num-iron ?ag) 1)
;              (not (present ?i)))
;)


;(:action pickup-diamond-pickaxe
; :parameters (?ag - agent ?i - diamond-pickaxe)
; :precondition (and (present ?i)
;                    (= (x ?i) (x ?ag))
;                    (= (y ?i) (y ?ag))
;                    (= (z ?i) (z ?ag)))
; :effect (and (increase (agent-num-diamond-pickaxe ?ag) 1)
;              (not (present ?i)))
;)


;(:action pickup-shears
; :parameters (?ag - agent ?i - shears)
; :precondition (and (present ?i)
;                    (= (x ?i) (x ?ag))
;                    (= (y ?i) (y ?ag))
;                    (= (z ?i) (z ?ag)))
; :effect (and (increase (agent-num-shears ?ag) 1)
;              (not (present ?i)))
;)


;(:action pickup-wool
; :parameters (?ag - agent ?i - wool)
; :precondition (and (present ?i)
;                    (= (x ?i) (x ?ag))
;                    (= (y ?i) (y ?ag))
;                    (= (z ?i) (z ?ag)))
; :effect (and (increase (agent-num-wool ?ag) 1)
;              (not (present ?i)))
;)


;(:action craft-diamond-pickaxe
;    :parameters ( ?ag - agent )
;    :precondition ( and
;                      ( > (agent-num-stick ?ag) 2 )
;                      ( > (agent-num-diamond ?ag) 3 )
;                  )
;    :effect (and (increase (agent-num-diamond-pickaxe ?ag) 1))
;
;)

;(:action craft-shears
;    :parameters ( ?ag - agent )
;    :precondition ( and
;                      ( > (agent-num-iron ?ag) 2 )
;                  )
;    :effect (and (increase (agent-num-shears ?ag) 1))
;
;)

(:action hit-obsidian-block
    :parameters (?ag - agent ?b - obsidian-block)
    :precondition (and (= (x ?b) (x ?ag))
                        (= (y ?b) (+ (y ?ag) 1))
                        (= (z ?b) (z ?ag))
                        (block-present ?b)
                        (< (block-hits ?b) 4))
                        ( > (agent-num-diamond-pickaxe) 1 )
    :effect (and (increase (block-hits ?b) 1))
    )

(:action destroy-obsidian-block
    :parameters (?ag - agent ?b - obsidian-block)
    :precondition (and (= (x ?b) (x ?ag))
                        (= (y ?b) (+ (y ?ag) 1))
                        (= (z ?b) (z ?ag))
                        (block-present ?b)
                        (= (block-hits ?b) 3))
                        ( > (agent-num-diamond-pickaxe) 1 )
    :effect (not (block-present ?b))
    )

)