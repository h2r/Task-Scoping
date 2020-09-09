<?xml version="1.0" encoding="UTF-8" ?>
    <Mission xmlns="http://ProjectMalmo.microsoft.com" xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance">
        <About>
            <Summary>{summary}</Summary>
        </About>

        <ModSettings>
            <MsPerTick>50</MsPerTick>
        </ModSettings>
        <ServerSection>
            <ServerInitialConditions>
                <Time>
                    <StartTime>1000</StartTime>
                    <AllowPassageOfTime>false</AllowPassageOfTime>
                </Time>
                <Weather>clear</Weather>
                <AllowSpawning>false</AllowSpawning>
                <AllowedMobs>Sheep</AllowedMobs>
            </ServerInitialConditions>
            <ServerHandlers>
                <FlatWorldGenerator generatorString="3;7,202*1,5*3,2;3;,biome_1" />
                <DrawingDecorator>
                    <DrawCuboid x1="-1" y1="199" z1="-12" x2="9" y2="202" z2="-199" type="bedrock"/>
<DrawCuboid x1="0" y1="200" z1="-11" x2="8" y2="201" z2="-200" type="air"/>
<DrawCuboid x1="11" y1="201" z1="-8" x2="11" y2="201" z2="-8" type="obsidian"/>
<DrawCuboid x1="10" y1="200" z1="-8" x2="10" y2="200" z2="-8" type="obsidian"/>
<DrawCuboid x1="10" y1="200" z1="0" x2="10" y2="200" z2="0" type="iron_ore"/>
<DrawItem x="1" y="200" z="0" type="stick"/>
<DrawItem x="1" y="200" z="-1" type="stick"/>
<DrawItem x="8" y="200" z="0" type="flint"/>
<DrawItem x="8" y="200" z="-1" type="flint"/>
<DrawItem x="8" y="200" z="-2" type="flint"/>
<DrawItem x="9" y="200" z="0" type="coal"/>
<DrawItem x="2" y="200" z="0" type="diamond"/>
<DrawItem x="2" y="200" z="-1" type="diamond"/>
<DrawItem x="2" y="200" z="-2" type="diamond"/>
<DrawItem x="3" y="200" z="0" type="apple"/>
<DrawItem x="3" y="200" z="-1" type="apple"/>
<DrawItem x="3" y="200" z="-2" type="apple"/>
<DrawItem x="4" y="200" z="0" type="potato"/>
<DrawItem x="4" y="200" z="-1" type="potato"/>
<DrawItem x="4" y="200" z="-2" type="potato"/>
<DrawItem x="4" y="200" z="-3" type="potato"/>
<DrawItem x="4" y="200" z="-4" type="potato"/>
<DrawItem x="5" y="200" z="0" type="pumpkin_pie"/>
<DrawItem x="5" y="200" z="-1" type="pumpkin_pie"/>
<DrawItem x="5" y="200" z="-2" type="pumpkin_pie"/>
<DrawItem x="5" y="200" z="-3" type="pumpkin_pie"/>
<DrawItem x="5" y="200" z="-4" type="pumpkin_pie"/>
<DrawItem x="6" y="200" z="0" type="bow"/>
<DrawItem x="6" y="200" z="-1" type="bow"/>
<DrawItem x="6" y="200" z="-2" type="bow"/>
<DrawItem x="6" y="200" z="-3" type="bow"/>
<DrawItem x="6" y="200" z="-4" type="bow"/>
<DrawItem x="7" y="200" z="0" type="rabbit"/>
<DrawItem x="7" y="200" z="-1" type="rabbit"/>
<DrawItem x="7" y="200" z="-2" type="rabbit"/>
<DrawItem x="7" y="200" z="-3" type="rabbit"/>
<DrawItem x="7" y="200" z="-4" type="rabbit"/>
                </DrawingDecorator>
               <ServerQuitWhenAnyAgentFinishes />
               <ServerQuitFromTimeUp timeLimitMs="120000"/>
            </ServerHandlers>
        </ServerSection>

        <AgentSection mode="Survival">
            <Name>The Q-Learner</Name>
            <AgentStart>
                <Placement x="0.0" y="200.0" z="0.0" pitch="50"/>
                <Inventory>
                    <InventoryItem type="diamond_pickaxe" slot="0"/>
                </Inventory>
            </AgentStart>
            <AgentHandlers>
                <ContinuousMovementCommands turnSpeedDegs="420"/>
                <ObservationFromRay/>
                <RewardForDamagingEntity>
                    <Mob type="Sheep" reward="1"/>
                    <Mob type="Pig" reward="-1"/>
                </RewardForDamagingEntity>
                <SimpleCraftCommands/>
                <ObservationFromNearbyEntities>
                    <Range name="entities" xrange="9'" yrange="2" zrange="-188" />
                </ObservationFromNearbyEntities>
                <ObservationFromFullStats/>{video_requirements}
            </AgentHandlers>
        </AgentSection>

    </Mission>