from __future__ import print_function
from __future__ import division
# ------------------------------------------------------------------------------------------------
# Copyright (c) 2016 Microsoft Corporation
#
# Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
# associated documentation files (the "Software"), to deal in the Software without restriction,
# including without limitation the rights to use, copy, modify, merge, publish, distribute,
# sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in all copies or
# substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
# NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
# NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
# DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
# ------------------------------------------------------------------------------------------------

# Demo of reward for damaging mobs - create an arena filled with pigs and sheep,
# and reward the agent positively for attacking sheep, and negatively for attacking pigs.
# Using this reward signal to train the agent is left as an exercise for the reader...
# this demo just uses ObservationFromRay and ObservationFromNearbyEntities to determine
# when and where to attack.

from builtins import range
from past.utils import old_div
import MalmoPython
import os
import random
import sys
import time
import json
import random
import errno
import math
import malmoutils
import uuid

malmoutils.fix_print()

# agent_hosts = [MalmoPython.AgentHost(), MalmoPython.AgentHost()]
agent_hosts = [MalmoPython.AgentHost()]
#
# malmoutils.parse_command_line(agent_host[0])


# recordingsDirectory = malmoutils.get_recordings_directory(agent_host)
video_requirements = ''
# '<VideoProducer><Width>860</Width><Height>480</Height></VideoProducer>' if agent_host[0].receivedArgument("record_video") else ''

def safeStartMission(agent_host, my_mission, my_client_pool, my_mission_record, role, expId):
    used_attempts = 0
    max_attempts = 5
    print("Calling startMission for role", role)
    while True:
        try:
            # Attempt start:
            agent_host.startMission(my_mission, my_client_pool, my_mission_record, role, expId)
            break
        except MalmoPython.MissionException as e:
            errorCode = e.details.errorCode
            if errorCode == MalmoPython.MissionErrorCode.MISSION_SERVER_WARMING_UP:
                print("Server not quite ready yet - waiting...")
                time.sleep(2)
            elif errorCode == MalmoPython.MissionErrorCode.MISSION_INSUFFICIENT_CLIENTS_AVAILABLE:
                print("Not enough available Minecraft instances running.")
                used_attempts += 1
                if used_attempts < max_attempts:
                    print("Will wait in case they are starting up.", max_attempts - used_attempts, "attempts left.")
                    time.sleep(2)
            elif errorCode == MalmoPython.MissionErrorCode.MISSION_SERVER_NOT_FOUND:
                print("Server not found - has the mission with role 0 been started yet?")
                used_attempts += 1
                if used_attempts < max_attempts:
                    print("Will wait and retry.", max_attempts - used_attempts, "attempts left.")
                    time.sleep(2)
            else:
                print("Other error:", e.message)
                print("Waiting will not help here - bailing immediately.")
                exit(1)
        if used_attempts == max_attempts:
            print("All chances used up - bailing now.")
            exit(1)
    print("startMission called okay.")

def safeWaitForStart(agent_hosts):
    print("Waiting for the mission to start", end=' ')
    start_flags = [False for a in agent_hosts]
    start_time = time.time()
    time_out = 120  # Allow a two minute timeout.
    while not all(start_flags) and time.time() - start_time < time_out:
        states = [a.peekWorldState() for a in agent_hosts]
        start_flags = [w.has_mission_begun for w in states]
        errors = [e for w in states for e in w.errors]
        if len(errors) > 0:
            print("Errors waiting for mission start:")
            for e in errors:
                print(e.text)
            print("Bailing now.")
            exit(1)
        time.sleep(0.1)
        print(".", end=' ')
    if time.time() - start_time >= time_out:
        print("Timed out while waiting for mission to start - bailing.")
        exit(1)
    print()
    print("Mission has started.")


def getMissionXML():
    # with open("/home/nishanth/Documents/planutils_stuff/OO-Scoping-IPC/examples/malmo/problems/prob_irrel_flint_with_pick.xml","r") as f:
    with open("/Users/michaelfishman/repos/scoping/OO-Scoping-IPC/examples/malmo/problems/prob_irrel_flint_with_pick.xml","r") as f:
        template = f.read()
    return template.format(summary="hi", video_requirements=video_requirements)

validate = True
client_pool = MalmoPython.ClientPool()
client_pool.add(MalmoPython.ClientInfo("127.0.0.1", 10000))
# client_pool.add(MalmoPython.ClientInfo('127.0.0.1', 10001))
print(client_pool)
my_mission = MalmoPython.MissionSpec(getMissionXML(), True)

experimentID = str(uuid.uuid4())
for i in range(len(agent_hosts)):
    safeStartMission(agent_hosts[i], my_mission, client_pool, MalmoPython.MissionRecordSpec(), i, experimentID)

safeWaitForStart(agent_hosts)
time.sleep(1)

# Non-watcher
agent_host = agent_hosts[0]
# I attempted to cast discrete motion into continuous motion by sending a stop command after a period of time, but this seems to give unreliable distances.

# Solution
move_sleep = 0.2
for i in range(7):
    print("Moving forward")
    agent_host.sendCommand("move 1")
    time.sleep(move_sleep)
for i in range(11):
    print("Moving right")
    agent_host.sendCommand("strafe 1")
    time.sleep(move_sleep)

print("Attacking")
agent_host.sendCommand("attack 1")
time.sleep(10)
agent_host.sendCommand("attack 0")

