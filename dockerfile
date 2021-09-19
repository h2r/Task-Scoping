FROM aiplanning/planutils

RUN apt-get update -y

RUN apt-get install git jq cmake g++ make -y

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
    && wget --quiet https://repo.anaconda.com/miniconda/Miniconda3-py37_4.10.3-Linux-x86_64.sh -O ~/miniconda.sh\
    && bash ~/miniconda.sh -fbp $INSTALL_PATH


# RUN eval "$(~/miniconda/bin/conda shell.bash hook)"
ENV PATH="~/miniconda/bin:${PATH}"



# Setup conda environment
RUN conda create -n scoping python=3.7

RUN conda activate scoping

RUN pip install pandas

WORKDIR ${SCOPING_DIR}

RUN pip install -e .

# Install Fast Downward

WORKDIR /
RUN git clone https://github.com/aibasel/downward.git
WORKDIR /downward
RUN ./build.py


# Install ENHSP-2020

RUN yes | enhsp-2020

WORKDIR ${SCOPING_DIR}