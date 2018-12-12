# Data compression algorithm
[LZSS](http://multimedia.ufp.pt/codecs/compressao-sem-perdas/codificacao-baseada-em-dicionarios/lzss/)

---
Encoding input requires the following steps:
1. Initialize the dictionary to a known value.
1. Read an uncoded string that is the length of the maximum allowable match.
1. Search for the longest matching string in the dictionary.
1. If a match is found greater than or equal to the minimum allowable match length:
    1. Write the encoded flag, then the offset and length to the encoded output. 
    1. Otherwise, write the uncoded flag and the first uncoded symbol to the encoded output. 
1. Shift a copy of the symbols written to the encoded output from the unencoded string to the dictionary.
1. Read a number of symbols from the uncoded input equal to the number of symbols written in Step 4.
1. Repeat from Step 3, until all the entire input has been encoded.

Decoding input requires the following steps: 
1. Initialize the dictionary to a known value.
1. Read the encoded/not encoded flag.
1. If the flag indicates an encoded string:
    1. Read the encoded length and offset, then copy the specified number of symbols from the dictionary to the decoded output. 
    1. Otherwise, read the next character and write it to the decoded output. 
1. Shift a copy of the symbols written to the decoded output into the dictionary.
1. Repeat from Step 2, until all the entire input has been decoded.
---

## **Question1:** Note that in the `FileSystemState` and the `FileStream` classes, all of the functions say they `read this`. Why is this important?
The `reads` clause gives a frame for the function, saying which objects the function may depend on.
The `reads` clause describes a set of objects. The function is then allowed to depend on any ﬁeld of any of those objects.
Dafny enforces the `reads` clause in the function body.
The Dafny function declaration is allowed to omit the body, in which case this deﬁnitional axiom is omitted and the function remains uninterpreted.
If body is omitted, the frame axiom still gives a partial interpretation of the function.

The reading frame of a function (or predicate) is all the memory locations that the function is allowed to read.
`reads` specifies a set of memory locations that the function is allowed to access.
Framing only applies to the heap, or memory accessed through references.


## **Question2:** Note that it isn’t possible to create new `FileSystemState` objects. What would problems might arise if this were possible?


## **Question3:** Semantically, what does it mean if you add preconditions (`requires`) to the `Main` method?
Dafny can't enforce something to be true before the `Main` method is called as Dafny can't control the environment where this code is going to be executed at compilation time.
Even though, adding preconditions to the `Main` method helps Dafny detect errors and prove correctness of all the code that is written inside of this `Main` method by guaranteeing that all preconditions of the methods used in the body hold. We could try to replace the `requires` with code verifications in the body of the `Main` method but as `env` is a `ghost` variable and all the objects of the `HostEnvironment` are also `ghost`, we can't use them in a non-`ghost` code, i.e. this `method`.
