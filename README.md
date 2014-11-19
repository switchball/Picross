# Picross

This repo is a algorithm writen in Haskell to solve Picross-like games. 
It is just a solver, not a game framework.

---

## Introduction

Picross is a kind of puzzle game, which uses horizontal and vertical line information to infer what the original picture is. You can try this at this [link](http://armorgames.com/play/132/armor-picross).

---

## Example

We may be presented the information like below:

```
          1   1
        2 3 4 3 2
      ┌-----------┐
    3 | ? ? ? ? ? |
1 1 1 | ? ? ? ? ? |
    5 | ? ? ? ? ? |
    3 | ? ? ? ? ? |
  1 1 | ? ? ? ? ? |
      └-----------┘
```

We can reduce it to the following one:

```
          1   1
        2 3 4 3 2
      -------------
    3 | . o o o . |
1 1 1 | o . o . o |
    5 | o o o o o |
    3 | . o o o . |
  1 1 | . o . o . |
      -------------
```

The numbers lying left and above indicate the consecutive pattern in the line (or column).

---

## Algorithm

### Idea

The inference often switches between line and column, that's what cross mean.

The solver algorithm also switch between line and colum. Each time it takes the number ahead, and the partial-known discs, trying to infer more discs. After that, transpose the discs and do this again, until all discs are recovered.

---

The key function in the code is `applyRule`, to apply on each line. It takes the numbers ahead the line (say it `Sequence`), and the partial-known discs (say it `[Disc]`), it will return the inferred discs or Nothing (say it `Maybe [Disc]`). If contradiction happens, `Nothing` is returned, that's why we use the `Maybe` keyword.

---

The thought of the function is straight forward. 

1. From the numbers ahead (i.e. `Sequence`), we can `generate` a list of discs satisfying this.
2. Then we `validate` the list, remove those lists which are contradictive with the known.
3. At last, we collect the common part of these survivors, `evidence` the fixed position.

The keyword, `generate`, `validate`, `evidence`, is what i excatly used in the algorithm, so as the meaning.

---

For example, with
```
  sequence = [2,2]
  discs    = [? o ? ? x ? ?]
```

where `?` is for the unknown one, `o` means the disc must exists, `x` means the disc must not exist.

```
   generate           validate               evidence
 [Init lists] -----> [Validated] ------->  [Common Part]
[o o x o o x x]     fail at pos=4
[o o x x o o x]     fail at pos=4
[o o x x x o o]    [o o x x x o o] --\   
[x o o x o o x]     fail at pos=4    |->  [? o ? x x o o]
[x o o x x o o]    [x o o x x o o] --/
[x x o o x o o]     fail at pos=1
```

Notice that we can evidence both `o`s and `x`s.

---

