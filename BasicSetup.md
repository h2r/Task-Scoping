These instructions are specifically for IPC 2018 Probabalistic Track. However, portions of these may be relevant to other
editions and formats of the competition.

STEPS:
1. Clone the RDDLSim library from the following link: <https://github.com/ssanner/rddlsim>
2. Follow the steps to install the library outlined here: <https://github.com/ssanner/rddlsim/blob/master/INSTALL.txt> <br />
  a. Specifically, run the compile script by simply doing `./compile`. <br />
  b. Next, make sure your CLASSPATH variable is set correctly. If you don't set this, you'll get an error message when 
     you attempt to ./run that certain java classes could not be located. <br />
  c. To set the CLASSPATH correctly, make sure the CLASSPATH environment variable points to the /lib folder under rddlsim.
     For example, run `export CLASSPATH=~/Documents/GitHub/rddlsim/lib` <br />
3. Install the specific version of Singularity that you'll need. Instructions on how to do this from the IPC committee can be
   found here: <https://ipc2018-probabilistic.bitbucket.io/>. Scroll down to the 'Details on Singularity' section and 
   check under the 'How do I install Singularity on my machine?' section.
4. Now, download/clone one of the planners from the IPC (such as PROST-DD: <https://bitbucket.org/ipc2018-probabilistic/prost-dd-1/src/ipc2018-disc-mdp/>).
   This will probably come with a Singularity file, which is critical for the next steps.
5. Run the following command `sudo singularity build planner.img your-directory-here/Singularity`. Replace the 
   'your-directory-here' with your actual directory structure. This will probably take a while to complete because it will 
   install an OS and all dependencies necessary for the code within the Singularity image.
6. Once this is done, you need to run the rddlsim server. Pick a rddl domain file (or folder) you'd like to run and move 
   it into the files directory under your local rddlsim repository. Then, run the following command: `./run rddl.competition.Server files/academic-advising/`.
   Here, the 'academic-advising' folder is a domain from the IPC that was moved under rddlsim/files. Now, your rddlsim server 
   should be up and running.
7. Open a new terminal and navigate to the directory containing your planner.img file. Run the following sequence of commands: <br />
  a. `mkdir rundir` <br />
  b. `RUNDIR="$(pwd)/rundir"` <br />
  c. `singularity run -C -H $RUNDIR planner.img academic_advising_mdp__1 2323`. Replace the 'academic_advising_mdp__1' with 
      whatever rddl file (that the server needs to have loaded in step 6) you'd like to run on. <br />
8. TA-DA! Watch the planner run on the provided domain and print our stats!
