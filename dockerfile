FROM aiplanning/planutils

# build command:
# docker build . -t scoping:sans_enhsp --progress=plain
# --progress-plain is needed to see echos. See https://stackoverflow.com/a/64932706
# Run command:
# docker run -it scoping:sans_enhsp /bin/bash

RUN apt-get update -y && echo "~~apt-get updated"

RUN apt-get install git jq cmake g++ make -y && echo "~~apt-get installed"

# Copy Scoping repo onto image
ENV SCOPING_DIR=/scoping_supplement/scoping

COPY ./ ${SCOPING_DIR}

# Install Conda

# From https://stackoverflow.com/a/57617879 (and other places)
RUN INSTALL_PATH=~/miniconda \
    && echo "~~~~~~Set miniconda INSTALL_PATH~~~~~~" \
    && wget --quiet https://repo.anaconda.com/miniconda/Miniconda3-py37_4.10.3-Linux-x86_64.sh -O ~/miniconda.sh\
    && echo "~~~~~~wgot miniconda installer"\
    && bash ~/miniconda.sh -fbp $INSTALL_PATH\
    && echo "~~~~~~Ran miniconda installer~~~~~~"\
    && PATH=$INSTALL_PATH/bin:$PATH\
    && echo "~~~~~~updated path to include conda~~~~~~"\
    && conda init bash\
    && echo "~~~~~~ran conda init bash~~~~~~"\
    && . ~/.bashrc\
    && echo "~~~~~~sourced .bashrc~~~~~~"\
    && conda create -n scoping python=3.7\
    && echo "~~~~~~created conda environment~~~~~~"\
    && conda activate scoping\
    && echo "~~~~~~activated conda environment~~~~~~"\  
    && pip install pandas\
    && echo "~~~~~~installed pandas~~~~~~"\
    && cd ${SCOPING_DIR}\
    && echo "~~~~~~cd into scoping directory~~~~~~"\
    && pip install -e .\
    && echo "~~~~~~installed scoping repo~~~~~~"


# Install Fast Downward

WORKDIR /
RUN git clone https://github.com/aibasel/downward.git
WORKDIR /downward
RUN ./build.py


# Install ENHSP-2020 (TODO make this work!)
# ERROR  : Failed to unshare root file system: Operation not permitted

# RUN yes | enhsp-2020

WORKDIR ${SCOPING_DIR}