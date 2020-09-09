# CP2020-Models
Models used for generating the results for my CP2020 paper

Conference: https://cp2020.a4cp.org/


Paper: [[Springer](https://rdcu.be/b6XYu)] [[Preprint](https://www.researchgate.net/publication/344136812_Aggregation_and_Garbage_Collection_for_Online_Optimization)]  


Talk: [[YouTube](https://youtu.be/xwYy736sEGo)]


Personal webpage: https://ekalexander.github.io

# How to use the models?

These models are "update-models", meaning that they require as input: previously known (sol_) and newly added (new_) data, as well as previous decisions (sol_) of previously known decision variables. The idea is to create a (separate from this) dynamic problem simulator (or from real observations) that iteratively calls an update-model to get the updated decisions.
