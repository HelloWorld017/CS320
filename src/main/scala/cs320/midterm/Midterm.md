# CS320 Midterm
CS320 (Programming Language) Midterm Essay
> 20190146 Kim Yohan

## Watching a Video

### Summary

It is a presentation about how the language should be designed.

He said that there are small languages and large languages, and small languages can't do the jobs right and large languages have too much time to show up.

So, he said that the main goal in language is how to grow; it should be start small and grow. And, he said that there are two kinds of growth; changing vocabularies and changing rules. While saying this, he mentioned about library and he said that it should be looked as primitive of language while it should let work done as designed at start.

Also, he provided two styles of growing a programming language: cathedral style and bazaar style. The cathedral style is that there is one grand plan, one designer and take many years. The bazaar style is no one plan and many users, who really work with it, contribute and grow as time goes by.

It doesn't mean that design has no use. Based on the metaphor of two styles, he insisted that a language design should be a pattern to grow with users.
<!-- There are many needs and if there is a big language that do all jobs, the cathedral-style in his word, it might have a long time and other small languages will take its place. -->

### Opinion
First, I thought that what he talk makes sense as I felt that there are some language, which have many potential to grow than other languages, because some of its design allow it. For example, the python, supports operation overloading, which is a feature mentioned in the presentation also, and some library like numpy, which utilizes slicing notation, looks as a primitive of language.

And, I also felt that growing by changing rule should be careful. For example, there are many users abusing the operator overloading and making an awful debugging experience. And I guess that it is why he said that we should design a way of doing, instead of not to design.

Finally, as I could recall how nice language grow with users, like PEP and TC39 Proposals while listening to his presentation, I could feel why growing language is important.

<!-- But, second, I thought that operation over -->

And it might not be a meaningful opinion for this video, but I was really surprised at he is actually done growing language in his presentation, using one-syllable words as a base language and defining words and rules.

## Choosing a Feature
> Object & Prototype-based Inheritance

### Description
I would like to add an `Object`, which is a mutable value and able to store structured data. It contains other values in form of map from a key to a value.

Also I would like to add a `Prototype-based Inheritance`, which is creating a new object by extending properties of an existing object.

For example, assume that I try to get value with key k, from an object o, which is extended with o1, o2, ..., on. Then, if o have a value for k, return it. If else, try it for o1, o2, ..., on. So, if we change a value for a key in o2, and o and o1 doesn't have the key, the values for the key changes for o and o1, too.

Using this, we can implement the polymorphism, like defining base object and extending it with some methods overriden. Also, we can define methods in prototype, create a object which contains value and call the methods which is in the prototype.

### Code Examples
```kotlin
val AnimalPrototype = {};
set AnimalPrototype.constructor = (this, age) =>
	set this.age = age;
	this;
set AnimalPrototype.age = 0;
set AnimalPrototype.newYear = (this) =>
	set this.age = this.age + 1; this.age;

val Animal = class [AnimalPrototype];

val ImmortalAnimalPrototype = {extends [AnimalPrototype]};
set ImmortalAnimalPrototype.constructor = (this) =>
	set this.age = 9999;
	this;
set ImmortalAnimalPrototype.newYear = (this) => this.age;

val ImmortalAnimal = class [ImmortalAnimalPrototype];

val myAnimal = Animal(0);
val immortalJellyfish = ImmortalAnimal();

myAnimal->newYear() + immortalJellyfish->newYear()
```
It creates two class: Animal and ImmortalAnimal, which is extended from Animal. The Animal object has age property, newYear method, and the `constructor` method, which serves as a constructor.

The ImmortalAnimal overrides its constructor and newYear method, modifying its mechanism to being old to fix its age at 9999. It's an example of polymorphism implemented using this feature.

It creates myAnimal and immortableJellyfish, from the classes and calls the "newYear" method, which are defined in their prototype.


### Links to Materials

The features are chosen from object & prototype in ECMAScript and table & metatable in Lua slightly.

* [ECMAScript Specification#Object Type](https://tc39.es/ecma262/#sec-object-type) for Object
* [ECMAScript Specification#Objects](https://tc39.es/ecma262/#sec-objects) for Prototype
* [Lua Manual#Metatables](https://www.lua.org/manual/5.3/manual.html#2.4)
	* As it can extend object by setting metatable, as it can define `__index` function.

## Growing a Language
I have chosen FIBER, the Project 1 Language, as a base language. And I've removed Tuples, Lists, Type Checking for simplicity. I'll call it as FIBER<sub>2</sub>.

### Justification
There are many occasion when a structured data is needed. For example, we might need to represent a graphical object, which contains x, y, colors, and much more properties and some methods like translate.

With using FIBER Language, we should represent it as a tuple or list, or many variables. But as they doesn't have any names, changing a certain value from the represented data is not intuitive. Also, if there are some cases when we need to change data while coding, and if we use only tuples or list, we should change whole index values.

<!-- Also, we have many occasions to do works with polymorphism, hoping calling same method name works for lots of types. For example, if we make a function which gets age of animal, we hope same method name

If we use FIBER language, we should define multiple functions use this prototype-based inheritance, for ex -->

 Finally, if we need to create same structured data over and over, we should write the default properties of object over and over, but using this feature, we can just make an object with prototype.

So I think the Object and Prototype is needed.

### Abstract Syntax
Abstract Syntax, which is extended from FIBER<sub>2</sub> is shown like this:

$$
\begin{aligned}
Expression\quad e\  ::=&\ \quad \{\} &\text{(new object)} \\
   & |\quad e.x & \text{(get value)} \\
   & |\quad set\ e.x = e;e& \text{(set value)} \\
   & |\quad \{extend\ e\}& \text{(new object from proto)} \\
   & |\quad class[e]& \text{(new class from proto)} \\
   & |\quad e\to x & \text{(get method)} \\
   & |\quad v & \text{(internal use of value)}\\\\
   & |\quad ... & \text{(inherited from FIBER}_2\text{)}
\end{aligned}
$$

Addr, ProtoKey, Key, Object, ObjectStore, Environment and Value are shown like this:
$$
\begin{aligned}
Addr & \quad a & \in & \quad \Bbb{A} \\
ProtoKey & \quad p & ::= &\quad \text{\$Prototype}\\
Key & \quad k & \in & \quad \Bbb{K} \\
 & \quad k & ::= &\quad  p\  |\ x\\
Value & \quad v & \in &\quad \Bbb{V} \\
 & \quad v & ::= &\quad n\  |\ b\ |\ a\ |\ \langle\lambda x \cdots x.e, \sigma \rangle \\
Object & \quad o & \in & \quad \Bbb{O} \\
 & \quad o & ::= & \quad \{x= v, \cdots, x= v\} \\
ObjectStore & \quad M & \quad \in & \quad \Bbb{A}  \xrightarrow \text{fin} \Bbb{O} \\
Environment & \quad \sigma  & \in & \quad Id \xrightarrow \text{fin} \Bbb{V}
\end{aligned}
$$

### Operational Semantics
A value is either an integer, a boolean value and an address of object, which is denoted by $a$ and has an address of actual object value.

An ObjectStore is a finite map from address to object.
The operational semantics added by this features are shown like this:

* This denotes that creating object add an entry to the object store and return its address.
$$
\begin{array}{c}
	a \notin Domain(M) \\
	\hline
	\sigma, M \vdash \{\} \Rightarrow a, M[a \to \{\}]
\end{array}
$$

* This denotes that set value for non-existing key in object adds key = value to the object and interpret the body expression.
$$
\begin{array}{c}
	\sigma, M \vdash e_1 \Rightarrow a,M_1 \qquad
	a \in Domain(M_1) \qquad
	\sigma, M_1 \vdash e_2 \Rightarrow v,M_2 \\
	M_2(a) = \{x=v_1,k_1=v_2,\cdots,k_n=v_{n+1}\}  \\
	M_2' =M_2[a \to \{x = v, k_1 = v_2, \cdots k_n = v_{n+1}\}] \qquad
	e_3,M_2'\vdash v_r, M_3 \\
	\hline
	\sigma, M \vdash set\ e_1.x = e_2;e_3 \Rightarrow v_r, M_3
\end{array}
$$

* This denotes that set value for existing key in object replaces key = value of the object and interpret the body expression.
$$
\begin{array}{c}
	\sigma, M \vdash e_1 \Rightarrow a,M_1\qquad
	a \in Domain(M_1) \qquad
	\sigma, M_1 \vdash e_2 \Rightarrow v,M_2 \\
	M_2(a) = \{k_1=v_1,\cdots,k_n=v_n\}  \qquad
	x \notin \{k_1, \cdots, k_n\} \\
	M_2' =M_2[a \to \{x = v, k_1 = v_1, \cdots k_n = v_n\}] \qquad
	e_3,M_2'\vdash v_r, M_3 \\
	\hline
	\sigma, M \vdash set\ e_1.x = e_2;e_3 \Rightarrow v_r, M_3
\end{array}
$$

* This denotes that get key, when key is not in object, traverses the prototype chain and returns its value.
$$
\begin{array}{c}
	\sigma, M \vdash e \Rightarrow a_1,M_1\qquad
	a_1, \cdots, a_{n+1} \in Domain(M_1) \\
	M_1(a_1) = \{p = a_2, x_{11} = v_{11}, \cdots, x_{1i_1} = v_{1i_1}\} \\
	\cdots \\
	M_1(a_n) = \{p = a_{n+1}, x_{n1} = v_{n1}, \cdots, x_{ni_n} = v_{ni_n}\} \\
	M_1(a_{n+1}) = \{x = v, x_{(n+1)1} = v_{(n+1)1}, \cdots, x_{(n+1)i_{n+1}} = v_{(n+1)i_{n+1}}\}\\
	x\neq x_{11}, \cdots, x \neq x_{1i_1} \quad \cdots \quad
	x \neq x_{(n+1)1}, \cdots, x \neq x_{(n+1)i_{n+1}} \\
	\hline
	\sigma, M \vdash e.x \Rightarrow v, M_1
\end{array}
$$

* This denotes that get key, when key in object, returns its value.
$$
\begin{array}{c}
	\sigma, M \vdash e \Rightarrow a,M_1\qquad
	a \in Domain(M_1) \qquad
	M_1(a) = \{x = v, x_1 = v_1, \cdots x_n = v_n\} \\
	\hline
	\sigma, M \vdash e.x \Rightarrow v, M_1
\end{array}
$$

* This denotes an internal usage of value as expr. (`ValueE`)
$$
\begin{array}{c}
	\sigma, M \vdash v \Rightarrow v,M
\end{array}
$$
* This denotes that extending an object returns an address pointing an object, which "$Prototype" is address of extended object.
$$
\begin{array}{c}
	\sigma, M \vdash e \Rightarrow a_1,M_1\qquad
	a \notin Domain(M_1) \qquad
	M_2 = M_1[a \to \{p = a_1\}]\\
	\hline
	\sigma, M \vdash \{extend\ e\} \Rightarrow a, M_2
\end{array}
$$

* This denotes that getting method is a sugar of wrap function with first default parameter of address of object.
$$
\begin{array}{c}
	\sigma, M \vdash e \Rightarrow a,M_1\qquad
	\sigma, M_1 \vdash a.x \Rightarrow v,M_2 \qquad
	v = \langle\lambda x_1, \cdots, x_n.e,\sigma' \rangle\\
	\hline
	\sigma, M \vdash e\to x \Rightarrow \langle \lambda x_2, \cdots, x_n.v(a, x_2, \cdots, x_n),\sigma \rangle, M_2
\end{array}
$$
* This denotes that getting class is a sugar of wrap function of constructor with first default parameter of address of object.
$$
\begin{array}{c}
	\sigma, M \vdash e \Rightarrow a,M_1\qquad
	\sigma, M_1 \vdash a.\text{constructor} \Rightarrow v,M_2 \\
	v = \langle\lambda x_1, \cdots, x_n.e,\sigma' \rangle\\
	\hline
	\sigma, M \vdash class[e] \Rightarrow \langle \lambda x_2, \cdots, x_n.v(\{extend\ a\}, x_2, \cdots, x_n),\sigma \rangle, M_2
\end{array}
$$

#### Inherited Semantics
* $$\sigma, M \vdash e \Rightarrow v, M$$
* $$
\begin{array}{c}
	x \in Domain(\sigma) \\
	\hline
	\sigma, M \vdash x \Rightarrow \sigma(x), M
\end{array}
$$
* $$\sigma, M \vdash n \Rightarrow n, M$$
* $$\sigma, M \vdash b \Rightarrow b, M$$
* $$
\begin{array}{c}
	\sigma, M \vdash e_1 \Rightarrow n_1, M_1 \qquad
	\sigma, M_1 \vdash e_2 \Rightarrow n_2, M_2 \\
	\hline
	\sigma, M \vdash e_1 + e_2 \Rightarrow n_1 + n_2, M_2
\end{array}
$$
* $$
\begin{array}{c}
	\sigma, M \vdash e_1 \Rightarrow n_1, M_1 \qquad
	\sigma, M_1 \vdash e_2 \Rightarrow n_2, M_2 \\
	\hline
	\sigma, M \vdash e_1 \times e_2 \Rightarrow n_1 \times n_2, M_2
\end{array}
$$
* $$
\begin{array}{c}
	\sigma, M \vdash e_1 \Rightarrow n_1, M_1 \qquad
	\sigma, M_1 \vdash e_2 \Rightarrow n_2, M_2 \\
	\hline
	\sigma, M \vdash e_1 \div e_2 \Rightarrow n_1 \div n_2, M_2
\end{array}
$$
* $$
\begin{array}{c}
	\sigma, M \vdash e_1 \Rightarrow n_1, M_1 \qquad
	\sigma, M_1 \vdash e_2 \Rightarrow n_2, M_2 \\
	\hline
	\sigma, M \vdash e_1\ mod\ e_2 \Rightarrow n_1\ mod\ n_2, M_2
\end{array}
$$
* $$
\begin{array}{c}
	\sigma, M \vdash e_1 \Rightarrow n_1, M_1 \qquad
	\sigma, M_1 \vdash e_2 \Rightarrow n_2, M_2 \\
	\hline
	\sigma, M \vdash e_1 = e_2 \Rightarrow n_1 = n_2, M_2
\end{array}
$$
* $$
\begin{array}{c}
	\sigma, M \vdash e_1 \Rightarrow n_1, M_1 \qquad
	\sigma, M_1 \vdash e_2 \Rightarrow n_2, M_2 \\
	\hline
	\sigma, M \vdash e_1 < e_2 \Rightarrow n_1 < n_2, M_2
\end{array}
$$
* $$
\begin{array}{c}
	\sigma, M \vdash e_1 \Rightarrow true, M_1 \qquad
	\sigma, M_1 \vdash e_2 \Rightarrow v, M_2 \\
	\hline
	\sigma, M \vdash if\ e_1 e_2 e_3 \Rightarrow v, M_2
\end{array}
$$
* $$
\begin{array}{c}
	\sigma, M \vdash e_1 \Rightarrow false, M_1 \qquad
	\sigma, M_1 \vdash e_3 \Rightarrow v, M_2 \\
	\hline
	\sigma, M \vdash if\ e_1 e_2 e_3 \Rightarrow v, M_2
\end{array}
$$
* $$
\begin{array}{c}
	\sigma, M \vdash e_1 \Rightarrow v_1, M_1 \qquad
	\sigma[x \mapsto v_1], M_1 \vdash e_2 \Rightarrow v_2, M_2 \\
	\hline
	\sigma, M \vdash val\ x = e_1\ in\ e_2 \Rightarrow v_2, M_2
\end{array}
$$
* $$\sigma, M \vdash \lambda x_1 \cdots x_i.e \Rightarrow \langle \lambda x_1 \cdots x_i.e, \sigma\rangle, M$$
* $$
\begin{array}{c}
	d_1 = def\ x_1(x_{11}, \cdots, x_{1i_1}) = e_1\quad \cdots \quad d_i = def\ x_i(x_{i1}, \cdots, x_{ii_i}) = e_i \\
	v_1 = \langle \lambda x_{11} \cdots x_{1i_1}.e_1, \sigma' \rangle \quad \cdots \quad  v_1 = \langle \lambda x_{i1} \cdots x_{ii_i}.e_i, \sigma' \rangle \\
	\sigma' = \sigma[x_1 \mapsto v_1, \cdots, x_i \mapsto v_i] \qquad \sigma', M \Rightarrow v, M_1 \\
	\hline \\
	\sigma, M \vdash d_1 \cdots d_i e \Rightarrow v, M_1
\end{array}$$
* $$
\begin{array}{c}
	\sigma, M e \Rightarrow \langle \lambda x_1 \cdots x_i.e', \sigma'\rangle, M_1\qquad \sigma, M_1\vdash e_1 \Rightarrow v_1, M_2 \quad \cdots \quad \sigma \vdash e_i \Rightarrow v_i, M_{i+1} \\
	\sigma'[x_1 \mapsto v_1, \cdots, x_i \mapsto v_i], M_{i+1} \vdash e' \Rightarrow v, M_r \\
	\hline \\
	\sigma, M \vdash e(e_1, \cdots, e_i) \Rightarrow v, M_r
\end{array}$$
