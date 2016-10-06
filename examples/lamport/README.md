# Example: Lamport's 1-bit mutual exclusion algorithm

The Petri net illustrated below models Lamport's 1-bit mutual exclusion algorithm \[Lam86, Fig. 1\]. Places on the left and right hand side correspond respectively to lines of the left and right procedures. Tokens indicate the current lines of code being executed. A token in the middle topmost place corresponds to `x` taking value `True`, while a token in the place underneath it corresponds to `x` taking value `False`. Similarly, the presence of a token in the two middle places below correspond to `y` taking respectively value `True` and `False`.

![Modelisation of Lamport's mutual exclusion algorithm](https://github.com/blondimi/qcover/blob/master/examples/lamport/petri_net.png)

`model.spec` represents this Petri net and asks whether the two critical sections can be reached at the same time, i.e. whether a marking with tokens in both red places can be reached. The algorithm can be proven safe by QCover by executing:
```
> python main.py model.spec
Safe
```

## References

Similar Petri nets and `.spec` modelisations also appear, e.g., in \[ELMMN14, Fig. 2\] and tools such as [mist](https://github.com/pierreganty/mist).

**\[ELMMN14\]** [Javier Esparza, Ruslán Ledesma-Garza, Rupak Majumdar, Philipp Meyer, Filip Nikšić. *An SMT-Based Approach to Coverability Analysis*. Proc. 26<sup>th</sup> International Conference on Computer Aided Verification (CAV), Springer, 2014](http://dx.doi.org/10.1007/978-3-319-08867-9_40).  Available online [here](https://www7.in.tum.de/um/bibdb/esparza/cav14-a.pdf).

**\[Lam86\]** [Leslie Lamport. *The Mutual Exclusion Problem: Part II – Statement and Solutions*. Journal of the ACM 33(2):327–348, 1986](http://dx.doi.org/10.1145/5383.5385). Available online [here](http://research.microsoft.com/en-us/um/people/lamport/pubs/mutual2.pdf).
