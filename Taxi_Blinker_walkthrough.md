# What's going on with the blinker?
# Stepping Through our Scoper

1. First iteration of "BFS with guaranatees"

## USED SKILLS
- pickup(p0)
- dropoff(p0) [somehow, this is repeated twice????]
- move_west with p0 in the taxi
- move_north with the blinker on and p0 in the taxi (THE SCOPER THINKS THIS AFFECTS passenger-x-curr(p0))
- move_north without the blinker on and p0 in the taxi [the blinker isn't explicitly set false, just not mentioned, and the scoper thinks this skill affects only passenger-y-curr(p0)]
- move_south with p0 in the taxi [somehow this is also repeated twice????]
- move_east with p0 in the taxi [somehow, this is repeated twice????]

[(AndList([taxi-x(t0) == passenger-x-curr(p0), taxi-y(t0) == passenger-y-curr(p0), Not(passenger-in-taxi(p0,t0)), Not(passenger-in-taxi(p1,t0))]),pickup(p0),['passenger-in-taxi(p0,t0)']), (AndList([passenger-in-taxi(p0,t0)]),dropoff(p0),['passenger-in-taxi(p0,t0)']), (AndList([passenger-in-taxi(p0,t0)]),dropoff(p0),['passenger-in-taxi(p0,t0)']),
(Or(And(passenger-in-taxi(p0,t0),
       Not(Or(And(WALL_X(w0) == passenger-x-curr(p0) - 1,
                  WALL_Y(w0) == passenger-y-curr(p0)))))),move_west(),['passenger-x-curr(p0)']),
(AndList([Or(And(passenger-in-taxi(p0,t0),
              taxi-blinker(t0),
              Not(Or(And(WALL_X(w0) == passenger-x-curr(p0) + 1,
                  WALL_Y(w0) == passenger-y-curr(p0) + 1)))))]),move_north(),['passenger-x-curr(p0)']),
(Or(And(passenger-in-taxi(p0,t0),
       Not(Or(And(WALL_X(w0) == passenger-x-curr(p0),
                  WALL_Y(w0) == passenger-y-curr(p0) + 1))))),move_north(),['passenger-y-curr(p0)']),
(Or(And(passenger-in-taxi(p0,t0),
       Not(Or(And(WALL_X(w0) == passenger-x-curr(p0) + 1,
                  WALL_Y(w0) == passenger-y-curr(p0)))))),move_east(),['passenger-x-curr(p0)']),
(Or(And(passenger-in-taxi(p0,t0),
       Not(Or(And(WALL_X(w0) == passenger-x-curr(p0) + 1,
                  WALL_Y(w0) == passenger-y-curr(p0)))))),move_east(),['passenger-x-curr(p0)']),
(Or(And(passenger-in-taxi(p0,t0),
       Not(Or(And(WALL_X(w0) == passenger-x-curr(p0),
                  WALL_Y(w0) == passenger-y-curr(p0) - 1))))),move_south(),['passenger-y-curr(p0)']),
(Or(And(passenger-in-taxi(p0,t0),
       Not(Or(And(WALL_X(w0) == passenger-x-curr(p0),
                  WALL_Y(w0) == passenger-y-curr(p0) - 1))))),move_south(),['passenger-y-curr(p0)'])]

## GUARANTEES
- taxi-x == passenger-x-curr(p0)???
- taxi-y(t0) == passenger-y-curr(p0)???
- p1 isn't in the taxi,
- p0 is in the taxi and there isn't a wall to the west???,
- p0 is in the taxi and the blinker is on and there isn't a wall to the northeast,
- p0 is in the taxi and there isn't a wall to the north
- p0 is in the taxi and there isn't a wall to the south

[taxi-x(t0) == passenger-x-curr(p0), taxi-y(t0) == passenger-y-curr(p0), Not(passenger-in-taxi(p1,t0)),
passenger-in-taxi(p0,t0),
Or(And(passenger-in-taxi(p0,t0),
       Not(Or(And(WALL_X(w0) == passenger-x-curr(p0) - 1,
                  WALL_Y(w0) == passenger-y-curr(p0)))))),
Or(And(passenger-in-taxi(p0,t0),
       taxi-blinker(t0),
       Not(Or(And(WALL_X(w0) == passenger-x-curr(p0) + 1,
                  WALL_Y(w0) == passenger-y-curr(p0) + 1))))),
Or(And(passenger-in-taxi(p0,t0),
       Not(Or(And(WALL_X(w0) == passenger-x-curr(p0),
                  WALL_Y(w0) == passenger-y-curr(p0) + 1))))),
Or(And(passenger-in-taxi(p0,t0),
       Not(Or(And(WALL_X(w0) == passenger-x-curr(p0),
                  WALL_Y(w0) == passenger-y-curr(p0) - 1)))))]

## DISCOVERED
- PASSENGERS_YOU_CARE_FOR is included but I'm not sure why / how....
- The goal statement is added
- Both passengers not in the taxi
- Taxi reaching p0 is added
- p0 is in the taxi
- All preconditions for movement actions (with p0 in the taxi) are added

[synth_Or(Not(PASSENGERS_YOU_CARE_FOR(p0)),
          And(Not(passenger-in-taxi(p0,t0)),
              passenger-x-curr(p0) == PASSENGER_GOAL_X(p0),
              passenger-y-curr(p0) == PASSENGER_GOAL_Y(p0))),
taxi-x(t0) == passenger-x-curr(p0),
taxi-y(t0) == passenger-y-curr(p0),
Not(passenger-in-taxi(p0,t0)),
Not(passenger-in-taxi(p1,t0)),
passenger-in-taxi(p0,t0),
Or(And(passenger-in-taxi(p0,t0),
       Not(Or(And(WALL_X(w0) == passenger-x-curr(p0) - 1,
                  WALL_Y(w0) == passenger-y-curr(p0)))))),
Or(And(passenger-in-taxi(p0,t0),
       taxi-blinker(t0),
       Not(Or(And(WALL_X(w0) == passenger-x-curr(p0) + 1,
                  WALL_Y(w0) == passenger-y-curr(p0) + 1))))),
Or(And(passenger-in-taxi(p0,t0),
       Not(Or(And(WALL_X(w0) == passenger-x-curr(p0),
                  WALL_Y(w0) == passenger-y-curr(p0) + 1))))),
Or(And(passenger-in-taxi(p0,t0),
       Not(Or(And(WALL_X(w0) == passenger-x-curr(p0) + 1,
                  WALL_Y(w0) == passenger-y-curr(p0)))))),
Or(And(passenger-in-taxi(p0,t0),
       Not(Or(And(WALL_X(w0) == passenger-x-curr(p0),
                  WALL_Y(w0) == passenger-y-curr(p0) - 1)))))]


2. First iteration of "Check guarantees"
## Guarantees
- All guarantees have been removed except for the fact that p1 is not in the taxi
[Not(passenger-in-taxi(p1,t0))]

## q
- All the previous guarantees except for p1 not in taxi are added to q

[taxi-x(t0) == passenger-x-curr(p0),
taxi-y(t0) == passenger-y-curr(p0),
passenger-in-taxi(p0,t0),
Or(And(passenger-in-taxi(p0,t0),
       Not(Or(And(WALL_X(w0) == passenger-x-curr(p0) - 1,
                  WALL_Y(w0) == passenger-y-curr(p0)))))),
Or(And(passenger-in-taxi(p0,t0),
       taxi-blinker(t0),
       Not(Or(And(WALL_X(w0) == passenger-x-curr(p0) + 1,
                  WALL_Y(w0) == passenger-y-curr(p0) + 1))))),
Or(And(passenger-in-taxi(p0,t0),
       Not(Or(And(WALL_X(w0) == passenger-x-curr(p0),
                  WALL_Y(w0) == passenger-y-curr(p0) + 1))))),
Or(And(passenger-in-taxi(p0,t0),
       Not(Or(And(WALL_X(w0) == passenger-x-curr(p0),
                  WALL_Y(w0) == passenger-y-curr(p0) - 1)))))]

3. Second iteration of "BFS with guarantees"
## USED SKILLS
- THE toggle_blinker() SKILL IS ADDED HERE!
- Also, all the movement skills when no passengers are in the taxi are added [again, there seem to be weird copies of skills?]

[(AndList([taxi-x(t0) == passenger-x-curr(p0), taxi-y(t0) == passenger-y-curr(p0), Not(passenger-in-taxi(p0,t0)), Not(passenger-in-taxi(p1,t0))]),pickup(p0),['passenger-in-taxi(p0,t0)']), (AndList([passenger-in-taxi(p0,t0)]),dropoff(p0),['passenger-in-taxi(p0,t0)']), (AndList([passenger-in-taxi(p0,t0)]),dropoff(p0),['passenger-in-taxi(p0,t0)']),
(Or(And(passenger-in-taxi(p0,t0),
       Not(Or(And(WALL_X(w0) == passenger-x-curr(p0) - 1,
                  WALL_Y(w0) == passenger-y-curr(p0)))))),move_west(),['passenger-x-curr(p0)']),
(AndList([Or(And(passenger-in-taxi(p0,t0),
       taxi-blinker(t0),
       Not(Or(And(WALL_X(w0) == passenger-x-curr(p0) + 1,
                  WALL_Y(w0) == passenger-y-curr(p0) + 1)))))]),move_north(),['passenger-x-curr(p0)']),
(Or(And(passenger-in-taxi(p0,t0),
       Not(Or(And(WALL_X(w0) == passenger-x-curr(p0),
                  WALL_Y(w0) == passenger-y-curr(p0) + 1))))),move_north(),['passenger-y-curr(p0)']),
(Or(And(passenger-in-taxi(p0,t0),
       Not(Or(And(WALL_X(w0) == passenger-x-curr(p0) + 1,
                  WALL_Y(w0) == passenger-y-curr(p0)))))),move_east(),['passenger-x-curr(p0)']),
(Or(And(passenger-in-taxi(p0,t0),
       Not(Or(And(WALL_X(w0) == passenger-x-curr(p0) + 1,
                  WALL_Y(w0) == passenger-y-curr(p0)))))),move_east(),['passenger-x-curr(p0)']),
(Or(And(passenger-in-taxi(p0,t0),
       Not(Or(And(WALL_X(w0) == passenger-x-curr(p0),
                  WALL_Y(w0) == passenger-y-curr(p0) - 1))))),move_south(),['passenger-y-curr(p0)']),
(Or(And(passenger-in-taxi(p0,t0),
       Not(Or(And(WALL_X(w0) == passenger-x-curr(p0),
                  WALL_Y(w0) == passenger-y-curr(p0) - 1))))),move_south(),['passenger-y-curr(p0)']),
(True,toggle_blinker(),['taxi-blinker(t0)']),
(AndList([Not(Or(And(WALL_X(w0) == taxi-x(t0), WALL_Y(w0) == taxi-y(t0) + 1)))]),move_north(),['taxi-y(t0)']), (AndList([Not(Or(And(WALL_X(w0) == taxi-x(t0), WALL_Y(w0) == taxi-y(t0) - 1)))]),move_south(),['taxi-y(t0)']), (AndList([Not(Or(And(WALL_X(w0) == taxi-x(t0), WALL_Y(w0) == taxi-y(t0) - 1)))]),move_south(),['taxi-y(t0)']), (AndList([Not(Or(And(WALL_X(w0) == taxi-x(t0) - 1, WALL_Y(w0) == taxi-y(t0))))]),move_west(),['taxi-x(t0)']), (AndList([taxi-blinker(t0), Not(Or(And(WALL_X(w0) == taxi-x(t0) + 1, WALL_Y(w0) == taxi-y(t0) + 1)))]), move_north(), ['taxi-x(t0)']),
(AndList([Not(Or(And(WALL_X(w0) == taxi-x(t0) + 1, WALL_Y(w0) == taxi-y(t0))))]), move_east(), ['taxi-x(t0)']), (AndList([Not(Or(And(WALL_X(w0) == taxi-x(t0) + 1, WALL_Y(w0) == taxi-y(t0))))]), move_east(), ['taxi-x(t0)'])]

## GUARANTEES
- Somehow "True" is now guaranteed???
- The taxi blinker is guaranteed as well
- It is now also guaranteed that there are not walls to the north, south, west or northeast of the taxi,
tho it is not guaranteed that there isn't a wall to the taxi's east

[Not(passenger-in-taxi(p1,t0)),
True,
Not(Or(And(WALL_X(w0) == taxi-x(t0),
           WALL_Y(w0) == taxi-y(t0) + 1))),
Not(Or(And(WALL_X(w0) == taxi-x(t0),
           WALL_Y(w0) == taxi-y(t0) - 1))),
Not(Or(And(WALL_X(w0) == taxi-x(t0) - 1,
           WALL_Y(w0) == taxi-y(t0)))),
taxi-blinker(t0),
Not(Or(And(WALL_X(w0) == taxi-x(t0) + 1,
           WALL_Y(w0) == taxi-y(t0) + 1)))]

## DISCOVERED
- "True" is now discovered???
- Everything else is the same as before, except now all conditions for the taxi's movement
without p0 in it are added.

[synth_Or(Not(PASSENGERS_YOU_CARE_FOR(p0)),
        And(Not(passenger-in-taxi(p0,t0)),
            passenger-x-curr(p0) == PASSENGER_GOAL_X(p0),
            passenger-y-curr(p0) == PASSENGER_GOAL_Y(p0))),
  taxi-x(t0) == passenger-x-curr(p0),
  taxi-y(t0) == passenger-y-curr(p0),
  Not(passenger-in-taxi(p0,t0)),
  Not(passenger-in-taxi(p1,t0)),
  passenger-in-taxi(p0,t0),
  Or(And(passenger-in-taxi(p0,t0),
      Not(Or(And(WALL_X(w0) == passenger-x-curr(p0) - 1,
      WALL_Y(w0) == passenger-y-curr(p0)))))),
  Or(And(passenger-in-taxi(p0,t0),
       taxi-blinker(t0),
       Not(Or(And(WALL_X(w0) == passenger-x-curr(p0) + 1,
                  WALL_Y(w0) == passenger-y-curr(p0) + 1))))),
  Or(And(passenger-in-taxi(p0,t0),
       Not(Or(And(WALL_X(w0) == passenger-x-curr(p0),
                  WALL_Y(w0) == passenger-y-curr(p0) + 1))))),
  Or(And(passenger-in-taxi(p0,t0),
       Not(Or(And(WALL_X(w0) == passenger-x-curr(p0) + 1,
                  WALL_Y(w0) == passenger-y-curr(p0)))))),
  Or(And(passenger-in-taxi(p0,t0),
       Not(Or(And(WALL_X(w0) == passenger-x-curr(p0),
                  WALL_Y(w0) == passenger-y-curr(p0) - 1))))),
  True,
  Not(Or(And(WALL_X(w0) == taxi-x(t0),
           WALL_Y(w0) == taxi-y(t0) + 1))),
  Not(Or(And(WALL_X(w0) == taxi-x(t0),
           WALL_Y(w0) == taxi-y(t0) - 1))),
  Not(Or(And(WALL_X(w0) == taxi-x(t0) - 1,
           WALL_Y(w0) == taxi-y(t0)))),
  taxi-blinker(t0),
  Not(Or(And(WALL_X(w0) == taxi-x(t0) + 1,
           WALL_Y(w0) == taxi-y(t0) + 1))),
  Not(Or(And(WALL_X(w0) == taxi-x(t0) + 1,
           WALL_Y(w0) == taxi-y(t0))))]

4. Second iteration of "Check Guarantees"
## GUARANTEES
- p1 is not in taxi
- True
[Not(passenger-in-taxi(p1,t0)), True]

## q
- All wall locations stopping taxi movement are added to q
- taxi-blinker is also added!!!
[Not(Or(And(WALL_X(w0) == taxi-x(t0),
           WALL_Y(w0) == taxi-y(t0) + 1))),
Not(Or(And(WALL_X(w0) == taxi-x(t0),
           WALL_Y(w0) == taxi-y(t0) - 1))),
Not(Or(And(WALL_X(w0) == taxi-x(t0) - 1,
           WALL_Y(w0) == taxi-y(t0)))),
taxi-blinker(t0),
Not(Or(And(WALL_X(w0) == taxi-x(t0) + 1,
           WALL_Y(w0) == taxi-y(t0) + 1)))]

5. Third iteration of "BFS with Guarantees"
## USED SKILLS
- Same as before

[(AndList([taxi-x(t0) == passenger-x-curr(p0), taxi-y(t0) == passenger-y-curr(p0), Not(passenger-in-taxi(p0,t0)), Not(passenger-in-taxi(p1,t0))]),pickup(p0),['passenger-in-taxi(p0,t0)']), (AndList([passenger-in-taxi(p0,t0)]),dropoff(p0),['passenger-in-taxi(p0,t0)']), (AndList([passenger-in-taxi(p0,t0)]),dropoff(p0),['passenger-in-taxi(p0,t0)']),
(Or(And(passenger-in-taxi(p0,t0),
       Not(Or(And(WALL_X(w0) == passenger-x-curr(p0) - 1,
                  WALL_Y(w0) == passenger-y-curr(p0)))))),move_west(),['passenger-x-curr(p0)']),
(AndList([Or(And(passenger-in-taxi(p0,t0),
       taxi-blinker(t0),
       Not(Or(And(WALL_X(w0) == passenger-x-curr(p0) + 1,
                  WALL_Y(w0) == passenger-y-curr(p0) + 1)))))]),move_north(),['passenger-x-curr(p0)']),
(Or(And(passenger-in-taxi(p0,t0),
       Not(Or(And(WALL_X(w0) == passenger-x-curr(p0),
                  WALL_Y(w0) == passenger-y-curr(p0) + 1))))),move_north(),['passenger-y-curr(p0)']),
(Or(And(passenger-in-taxi(p0,t0),
       Not(Or(And(WALL_X(w0) == passenger-x-curr(p0) + 1,
                  WALL_Y(w0) == passenger-y-curr(p0)))))),move_east(),['passenger-x-curr(p0)']),
(Or(And(passenger-in-taxi(p0,t0),
       Not(Or(And(WALL_X(w0) == passenger-x-curr(p0) + 1,
                  WALL_Y(w0) == passenger-y-curr(p0)))))),move_east(),['passenger-x-curr(p0)']),
(Or(And(passenger-in-taxi(p0,t0),
       Not(Or(And(WALL_X(w0) == passenger-x-curr(p0),
                  WALL_Y(w0) == passenger-y-curr(p0) - 1))))),move_south(),['passenger-y-curr(p0)']),
(Or(And(passenger-in-taxi(p0,t0),
       Not(Or(And(WALL_X(w0) == passenger-x-curr(p0),
                  WALL_Y(w0) == passenger-y-curr(p0) - 1))))),move_south(),['passenger-y-curr(p0)']),
(True,toggle_blinker(),['taxi-blinker(t0)']),
(AndList([Not(Or(And(WALL_X(w0) == taxi-x(t0),
           WALL_Y(w0) == taxi-y(t0) + 1)))]),move_north(),['taxi-y(t0)']), (AndList([Not(Or(And(WALL_X(w0) == taxi-x(t0),
           WALL_Y(w0) == taxi-y(t0) - 1)))]),move_south(),['taxi-y(t0)']), (AndList([Not(Or(And(WALL_X(w0) == taxi-x(t0),
           WALL_Y(w0) == taxi-y(t0) - 1)))]),move_south(),['taxi-y(t0)']), (AndList([Not(Or(And(WALL_X(w0) == taxi-x(t0) - 1,
           WALL_Y(w0) == taxi-y(t0))))]),move_west(),['taxi-x(t0)']),
(AndList([taxi-blinker(t0), Not(Or(And(WALL_X(w0) == taxi-x(t0) + 1,
           WALL_Y(w0) == taxi-y(t0) + 1)))]),move_north(),['taxi-x(t0)']),
(AndList([Not(Or(And(WALL_X(w0) == taxi-x(t0) + 1,
           WALL_Y(w0) == taxi-y(t0))))]),move_east(),['taxi-x(t0)']),
(AndList([Not(Or(And(WALL_X(w0) == taxi-x(t0) + 1,
           WALL_Y(w0) == taxi-y(t0))))]),move_east(),['taxi-x(t0)'])]

## GUARANTEES
- Same as in previous iteration of "Check Guarantees"
[Not(passenger-in-taxi(p1,t0)), True]

## DISCOVERED
- Same as before!

[synth_Or(Not(PASSENGERS_YOU_CARE_FOR(p0)),
          And(Not(passenger-in-taxi(p0,t0)),
          passenger-x-curr(p0) == PASSENGER_GOAL_X(p0),
          passenger-y-curr(p0) == PASSENGER_GOAL_Y(p0))),
taxi-x(t0) == passenger-x-curr(p0),
taxi-y(t0) == passenger-y-curr(p0),
Not(passenger-in-taxi(p0,t0)),
Not(passenger-in-taxi(p1,t0)),
passenger-in-taxi(p0,t0),
Or(And(passenger-in-taxi(p0,t0),
       Not(Or(And(WALL_X(w0) == passenger-x-curr(p0) - 1,
                  WALL_Y(w0) == passenger-y-curr(p0)))))),
Or(And(passenger-in-taxi(p0,t0),
       taxi-blinker(t0),
       Not(Or(And(WALL_X(w0) == passenger-x-curr(p0) + 1,
                  WALL_Y(w0) == passenger-y-curr(p0) + 1))))),
Or(And(passenger-in-taxi(p0,t0),
       Not(Or(And(WALL_X(w0) == passenger-x-curr(p0),
                  WALL_Y(w0) == passenger-y-curr(p0) + 1))))),
Or(And(passenger-in-taxi(p0,t0),
       Not(Or(And(WALL_X(w0) == passenger-x-curr(p0) + 1,
                  WALL_Y(w0) == passenger-y-curr(p0)))))),
Or(And(passenger-in-taxi(p0,t0),
       Not(Or(And(WALL_X(w0) == passenger-x-curr(p0),
                  WALL_Y(w0) == passenger-y-curr(p0) - 1))))),
True,
Not(Or(And(WALL_X(w0) == taxi-x(t0),
           WALL_Y(w0) == taxi-y(t0) + 1))),
Not(Or(And(WALL_X(w0) == taxi-x(t0),
           WALL_Y(w0) == taxi-y(t0) - 1))),
Not(Or(And(WALL_X(w0) == taxi-x(t0) - 1,
           WALL_Y(w0) == taxi-y(t0)))),
taxi-blinker(t0),
Not(Or(And(WALL_X(w0) == taxi-x(t0) + 1,
           WALL_Y(w0) == taxi-y(t0) + 1))),
Not(Or(And(WALL_X(w0) == taxi-x(t0) + 1,
           WALL_Y(w0) == taxi-y(t0))))]

6. Third iteration of "Check Guarantees"
## GUARANTEES
- Same Guarantees as previous iteration
[Not(passenger-in-taxi(p1,t0)), True]

## q
- Empty, so we're done
[]
