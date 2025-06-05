# EaaFuzz: A Neural Network-Based Fuzzing Framework with Sparse Encoding and Energy-Aware Adaptive Mutation
Eaafuzz is a kind of fuzzy testing of coverage rate. Through the energy-aware adaptive fuzzy testing method of sparse self-encoder, it is specially modeled for the “input key section” and optimizes the variation strategy to make the fuzzy testing more accurate and efficient.
## How to perform fuzzing with CIDFuzz
1 Download Miniconda installation script
```
wget https://repo.anaconda.com/miniconda/Miniconda3-latest-Linux-x86_64.sh
```
2 Create a new virtual environment named keras-env
```
bash Miniconda3-latest-Linux-x86_64.sh
```
3 Install TensorFlow 2.12.0
```
pip install tensorflow==2.12.0 keras==2.12.0
```
4 Use AFL to run for a period to generate the original seed training set Eaafuzz_in, and run Model training
```
python Model training.py
```
5 Run the Energy model to generate new seeds and energy models
```
python Energy model.py
```
6 Fuzz testing
```
./Fuzzing -i splice_seeds -o seeds -l 8041 ./xmllint @@
```

