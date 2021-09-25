FROM aiplanning/planutils

# build command:
# docker build . -t scoping --progress=plain --no-cache
# --progress-plain is needed to see echos. See https://stackoverflow.com/a/64932706

# Allow us to write to stdout and stderr while building.
# Coped from https://serverfault.com/questions/599103/make-a-docker-application-write-to-stdout
# forward request and error logs to docker log collector

RUN apt-get update -y && echo "~~apt-get updated"

RUN apt-get install git jq cmake g++ make -y && echo "~~apt-get installed"

# Copy Scoping repo onto image
ENV SCOPING_DIR=/scoping_supplement/scoping

COPY ./ ${SCOPING_DIR}

# Install Conda (TODO make this work!)
# RUN wget --quiet https://repo.anaconda.com/miniconda/Miniconda3-py37_4.10.3-Linux-x86_64.sh -O ~/miniconda.sh

# RUN sh ~/miniconda.sh -b -p /opt/conda

# # This command lets us use conda without restarting shell. (TODO It doesn't work, probably because each RUN creates a new shell. )
# RUN eval "$(~/miniconda/bin/conda shell.bash hook)"

# From https://stackoverflow.com/a/57617879
RUN INSTALL_PATH=~/miniconda \
    && echo "~~Set miniconda INSTALL_PATH" \
    && wget --quiet https://repo.anaconda.com/miniconda/Miniconda3-py37_4.10.3-Linux-x86_64.sh -O ~/miniconda.sh\
    && echo "~~wgot miniconda installer"\
    && bash ~/miniconda.sh -fbp $INSTALL_PATH\
    && echo "~~Ran miniconda installer"\
    # && RUN eval "$(~/miniconda/condabin/conda shell.bash hook)"\
    # && echo "~~Ran eval miniconda, which should let us use cona from within this RUN"\
    # # Can't find bashrc, so this doesn't work.
    && . ~/.bashrc\
    && echo "Sourced ~/.bashrc"\
    && conda create -n scoping python=3.7\
    && echo "created conda environment"\
    && conda activate scoping\
    && echo "activated conda environment"\  
    && pip install pandas\
    && echo "installed pandas"\
    && cd ${SCOPING_DIR}\
    && echo "cd into scoping directory"\
    && pip install -e .\
    && echo "installed scoping repo"


# ENV PATH="~/miniconda/bin:${PATH}"


# RUN pip install pandas

# WORKDIR ${SCOPING_DIR}

# RUN pip install -e .

# Install Fast Downward

WORKDIR /
RUN git clone https://github.com/aibasel/downward.git
WORKDIR /downward
RUN ./build.py


# Install ENHSP-2020

RUN yes | enhsp-2020

WORKDIR ${SCOPING_DIR}