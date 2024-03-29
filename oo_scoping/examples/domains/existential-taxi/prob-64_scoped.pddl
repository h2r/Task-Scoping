(define (problem TAXINUMERIC-64)
(:domain universal_multipasstaxi)
(:objects
	curly smoov edison isbell cornelius nero kaelbling perez levine abbeel nilsson fikes mcdermott vonNeumann turing urtasun garg shkruti agrawal pathak fidler tedrake finn bohg sadigh dragan srinivasa brooks mataric stone silver sridhar gu hausman anguelov sutskever krizhevsky goodfellow ng schulman bengio hinton lecunn schmidhuber mcilraith geffner bonet thiebeaux russell norvig muise roy brunskill velez nau traverso hilbert djikstra rumelhart minsky reddy mccarthy shannon sacerdoti - passenger
    t0 - taxi
)
(:init
    (= (taxi-x t0) 0)
    (= (taxi-y t0) 0)

    (not (in-taxi curly t0))
    (not (in-taxi smoov t0))
    (not (in-taxi edison t0))
    (not (in-taxi isbell t0))
    (not (in-taxi cornelius t0))
    (not (in-taxi nero t0))
    (not (in-taxi kaelbling t0))
    (not (in-taxi perez t0))
    (not (in-taxi levine t0))
    (not (in-taxi abbeel t0))
    (not (in-taxi nilsson t0))
    (not (in-taxi fikes t0))
    (not (in-taxi mcdermott t0))
    (not (in-taxi vonNeumann t0))
    (not (in-taxi turing t0))
    (not (in-taxi urtasun t0))
    (not (in-taxi garg t0))
    (not (in-taxi shkruti t0))
    (not (in-taxi agrawal t0))
    (not (in-taxi pathak t0))
    (not (in-taxi fidler t0))
    (not (in-taxi tedrake t0))
    (not (in-taxi finn t0))
    (not (in-taxi bohg t0))
    (not (in-taxi sadigh t0))
    (not (in-taxi dragan t0))
    (not (in-taxi srinivasa t0))
    (not (in-taxi brooks t0))
    (not (in-taxi mataric t0))
    (not (in-taxi stone t0))
    (not (in-taxi silver t0))
    (not (in-taxi sridhar t0))
    (not (in-taxi gu t0))
    (not (in-taxi hausman t0))
    (not (in-taxi anguelov t0))
    (not (in-taxi sutskever t0))
    (not (in-taxi krizhevsky t0))
    (not (in-taxi goodfellow t0))
    (not (in-taxi ng t0))
    (not (in-taxi schulman t0))
    (not (in-taxi bengio t0))
    (not (in-taxi hinton t0))
    (not (in-taxi lecunn t0))
    (not (in-taxi schmidhuber t0))
    (not (in-taxi mcilraith t0))
    (not (in-taxi geffner t0))
    (not (in-taxi bonet t0))
    (not (in-taxi thiebeaux t0))
    (not (in-taxi russell t0))
    (not (in-taxi norvig t0))
    (not (in-taxi muise t0))
    (not (in-taxi roy t0))
    (not (in-taxi brunskill t0))
    (not (in-taxi velez t0))
    (not (in-taxi nau t0))
    (not (in-taxi traverso t0))
    (not (in-taxi hilbert t0))
    (not (in-taxi djikstra t0))
    (not (in-taxi rumelhart t0))
    (not (in-taxi minsky t0))
    (not (in-taxi reddy t0))
    (not (in-taxi mccarthy t0))
    (not (in-taxi shannon t0))
    (not (in-taxi sacerdoti t0))

    (= (pass-x curly) 3329)
    (= (pass-x smoov) 3459)
    (= (pass-x edison) 1291)
    (= (pass-x isbell) 9723)
    (= (pass-x cornelius) 8523)
    (= (pass-x nero) 9621)
    (= (pass-x kaelbling) 3362)
    (= (pass-x perez) 5311)
    (= (pass-x levine) 7900)
    (= (pass-x abbeel) 9535)
    (= (pass-x nilsson) 9426)
    (= (pass-x fikes) 7785)
    (= (pass-x mcdermott) 2626)
    (= (pass-x vonNeumann) 3418)
    (= (pass-x turing) 2366)
    (= (pass-x urtasun) 1365)
    (= (pass-x garg) 6566)
    (= (pass-x shkruti) 4258)
    (= (pass-x agrawal) 6677)
    (= (pass-x pathak) 4924)
    (= (pass-x fidler) 8686)
    (= (pass-x tedrake) 3330)
    (= (pass-x finn) 914)
    (= (pass-x bohg) 8376)
    (= (pass-x sadigh) 5787)
    (= (pass-x dragan) 2703)
    (= (pass-x srinivasa) 5936)
    (= (pass-x brooks) 5117)
    (= (pass-x mataric) 3273)
    (= (pass-x stone) 8612)
    (= (pass-x silver) 7256)
    (= (pass-x sridhar) 1723)
    (= (pass-x gu) 39)
    (= (pass-x hausman) 6679)
    (= (pass-x anguelov) 7069)
    (= (pass-x sutskever) 4230)
    (= (pass-x krizhevsky) 637)
    (= (pass-x goodfellow) 848)
    (= (pass-x ng) 1154)
    (= (pass-x schulman) 8675)
    (= (pass-x bengio) 9735)
    (= (pass-x hinton) 4724)
    (= (pass-x lecunn) 4083)
    (= (pass-x schmidhuber) 8858)
    (= (pass-x mcilraith) 7303)
    (= (pass-x geffner) 4533)
    (= (pass-x bonet) 6230)
    (= (pass-x thiebeaux) 7667)
    (= (pass-x russell) 2473)
    (= (pass-x norvig) 9090)
    (= (pass-x muise) 1741)
    (= (pass-x roy) 4207)
    (= (pass-x brunskill) 4621)
    (= (pass-x velez) 4362)
    (= (pass-x nau) 4377)
    (= (pass-x traverso) 1720)
    (= (pass-x hilbert) 6788)
    (= (pass-x djikstra) 4274)
    (= (pass-x rumelhart) 508)
    (= (pass-x minsky) 6423)
    (= (pass-x reddy) 974)
    (= (pass-x mccarthy) 7354)
    (= (pass-x shannon) 2241)
    (= (pass-x sacerdoti) 3588)

    (= (pass-y curly) 3615)
    (= (pass-y smoov) 1262)
    (= (pass-y edison) 5037)
    (= (pass-y isbell) 4875)
    (= (pass-y cornelius) 7637)
    (= (pass-y nero) 1215)
    (= (pass-y kaelbling) 3284)
    (= (pass-y perez) 1361)
    (= (pass-y levine) 6594)
    (= (pass-y abbeel) 2694)
    (= (pass-y nilsson) 4641)
    (= (pass-y fikes) 2300)
    (= (pass-y mcdermott) 3593)
    (= (pass-y vonNeumann) 4590)
    (= (pass-y turing) 562)
    (= (pass-y urtasun) 4584)
    (= (pass-y garg) 257)
    (= (pass-y shkruti) 8022)
    (= (pass-y agrawal) 5821)
    (= (pass-y pathak) 78)
    (= (pass-y fidler) 4789)
    (= (pass-y tedrake) 1441)
    (= (pass-y finn) 2349)
    (= (pass-y bohg) 1420)
    (= (pass-y sadigh) 6959)
    (= (pass-y dragan) 8754)
    (= (pass-y srinivasa) 174)
    (= (pass-y brooks) 5105)
    (= (pass-y mataric) 5731)
    (= (pass-y stone) 1845)
    (= (pass-y silver) 6663)
    (= (pass-y sridhar) 2859)
    (= (pass-y gu) 6526)
    (= (pass-y hausman) 5668)
    (= (pass-y anguelov) 4891)
    (= (pass-y sutskever) 5929)
    (= (pass-y krizhevsky) 250)
    (= (pass-y goodfellow) 3614)
    (= (pass-y ng) 7332)
    (= (pass-y schulman) 3474)
    (= (pass-y bengio) 5456)
    (= (pass-y hinton) 8867)
    (= (pass-y lecunn) 5329)
    (= (pass-y schmidhuber) 6750)
    (= (pass-y mcilraith) 5265)
    (= (pass-y geffner) 2712)
    (= (pass-y bonet) 2319)
    (= (pass-y thiebeaux) 8469)
    (= (pass-y russell) 6595)
    (= (pass-y norvig) 7821)
    (= (pass-y muise) 3172)
    (= (pass-y roy) 2059)
    (= (pass-y brunskill) 3766)
    (= (pass-y velez) 4515)
    (= (pass-y nau) 4586)
    (= (pass-y traverso) 3200)
    (= (pass-y hilbert) 7811)
    (= (pass-y djikstra) 3246)
    (= (pass-y rumelhart) 3204)
    (= (pass-y minsky) 2545)
    (= (pass-y reddy) 13)
    (= (pass-y mccarthy) 5407)
    (= (pass-y shannon) 5989)
    (= (pass-y sacerdoti) 3512)

)
(:goal (and
    (= (pass-y curly) 10000)
	(= (pass-x curly) 9000)
    (not (in-taxi curly t0))
	
    )
)

)