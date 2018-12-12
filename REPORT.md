# Data compression algorithm
## LZSS
    
### Some references:
* http://michael.dipperstein.com/lzss/
* http://multimedia.ufp.pt/codecs/compressao-sem-perdas/codificacao-baseada-em-dicionarios/lzss/
* https://en.wikipedia.org/wiki/Lempel%E2%80%93Ziv%E2%80%93Storer%E2%80%93Szymanski

---

## Some notes about the implementation


All the methods related with the compression and decompression of bytes are in the class [LZSS](./compression/LZSS.dfy).

Encoding input requires the following steps (method `Encode` of class [LZSS](./compression/LZSS.dfy)):

Decoding input requires the following steps (method `Decode` of class [LZSS](./compression/LZSS.dfy)):

---

## **Question1:** Note that in the `FileSystemState` and the `FileStream` classes, all of the functions say they `reads this`. Why is this important?
The `reads` clause gives a frame for the function, saying which objects the function may depend on. The function is then allowed to depend on any ﬁeld of any of those objects.
The reading frame of a function (or predicate) is all the memory locations (only applies to the heap) that the function is allowed to read.
Considering the Hoare Triple, the `{:axiom}` attribute of these functions and the fact that they don't declare any precondition (defaults to `true`), we know that these functions hold for all the states of the application.
Given the `reads this` and with the body omitted we know that this frame axiom still gives a partial interpretation of the function thus reducing the state of the application where these functions should hold. In the end, this will help Dafny verify code more quickly.


## **Question2:** Note that it isn’t possible to create new `FileSystemState` objects. What would problems might arise if this were possible?


## **Question3:** Semantically, what does it mean if you add preconditions (`requires`) to the `Main` method?
Dafny can't enforce something to be true before the `Main` method is called as Dafny can't control the environment where this code is going to be executed at compilation time.
Even though, adding preconditions to the `Main` method helps Dafny detect errors and prove correctness of all the code that is written inside of this `Main` method by guaranteeing that all preconditions of the methods used in the body hold. We could try to replace the `requires` with code verifications in the body of the `Main` method but as `env` is a `ghost` variable and all the objects of the `HostEnvironment` are also `ghost`, we can't use them in a non-`ghost` code, i.e. this `method`.
