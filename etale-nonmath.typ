#import "void-import.typ": *
// #show: void-style

#let acknowledgements = [
  I hold sincere gratitude towards Prof. Koji Shimizu, who gave a course on etale cohomology in 2025 Fall in Tsinghua University. This document is based on his course, and I am grateful for such an accessible introduction to etale cohomology. 

  I also hold sincere gratitude towards the authors of the large number of accessible references already present on the topic of etale cohomology. Without consulting these materials and comparing their approaches, I couldn't have made the roadmap to etale cohomology clear and conceptual. These references are: Stacks Project @cite-SP, Lei Fu (扶磊) @cite-lei-fu, Freitag-Kiehl @cite-freitag-kiehl, Deligne's Arcata notes @cite-deligne-arcata, Milne @cite-milne-lectures and @cite-milne-etale, and of course the original SGA books @cite-SGA1, @cite-SGA4 and @cite-SGA4half.

  I would also like to thank my friends, who gave me consistent support, helpful discussions and advice throughout the construction of this document. My friend Irisu (`Irisu7777h@gmail.com`) helped me develop a high-level understanding of some large theorems (Smooth Base Change, and also the setup of the Weil conjectures), and pointed out multiple technicalities that I should keep in mind (such as one in @chapter-etale-sheaves). #if (not compile-cfg.cover-pic.censored) [He also kindly created the beautiful artwork on the cover page. ]My friend Sean (#link("https://triangulated-ruler.github.io/index.html", text(fill: blue.darken(25%))[homepage])) checked my independent proof of topological invariance in @sect-topological-invariance and had some discussions with me around the compatibility conditions in @chapter-lower-shriek. My friend and roommate Darpaz endured my keyboard noise whilst I was typing this document through many nights, and executed my impromptu suggestions to order food delivery at 0 o'clock. My friends Mark, AppoloniusSun (#link("https://apolloniussun.github.io/", text(fill: blue.darken(25%))[homepage])), VByed7 (#link("https://vbyed7.github.io/VByed7/", text(fill: blue.darken(25%))[homepage])), KahlerManifold and SimplicialCat (#link("https://simplicialcat.github.io/", text(fill: blue.darken(25%))[homepage])) listened to my explanation on various topics several times, following approaches adopted in this document, which provided valuable opportunities for me to check my understanding and the validity of these approaches.#footnote[All of these names are pseudonyms because I am not by default exposing the identities of my friends.]

  Last but not least, the AI models I used played a crucial role in constructing the document. I will discuss their roles in the disclosure of AI usage section. They have answered my random informal questions that would be deemed too uninspiring, technical or repetitive for a human answerer. They also refined my understanding and did much painstaking work. For example, ChatGPT 5.6 Terra found 996 typos within this document, of which I accepted 956 and rejected 40. I genuinely cannot imagine how an author could eliminate typos so systematically without AI assistance. 
]

#let disclosure-of-ai-usage = [
  This document was prepared with help from the following AI models: ChatGPT 5.6 Sol, ChatGPT 5.6 Terra, ChatGPT 5.5, Gemini 3.1, DeepSeek V4 Pro. 

  Regarding their role, I asked them to help me understand the underlying ideas for many proofs and also to explain details of proofs that I did not understand. I also used them to do hard work such as finding and correcting typos, finding sketchy paragraphs that require attention, and proposing resolutions of questionable paragraphs and todos. 

  Nevertheless, I typed 99% of the text within this document myself, and I did manually check each of the few blocks of text proposed by an AI model. I hereby declare that, as far as I know, this document consists of sound mathematics that I can personally agree with and is free of AI hallucinations. 
]

#let preface = [
  This document started as the lecture notes for the 2025 Fall course by Prof. Koji Shimizu, as mentioned in the acknowledgements. Over time, I used the original lecture notes as a skeleton and rewrote most of it while expanding in my own words, to the point that it should be considered an original creation of myself. 
  
  This material is designed to be especially suitable for speedrunning the theory of etale cohomology, even for people with no particularly strong background in or enthusiasm for algebraic geometry. The title _Etale Cohomology (Any%)_ was also coined with this purpose in mind, where "(Any%)" refers to a category of video game speedruns that requires completing only the main goals of the game as quickly as possible, rather than achieving 100% completion. 

  Now you might have asked: This document is over 500 pages long. How can this possibly be called a speedrun? 

  Personally, I believe that for mathematical texts of length below a certain large threshold, length introduces clarity, and compression is accompanied by obfuscation. I've arranged the document in such a way that a reader can obtain a good enough understanding of etale cohomology in a single sequential pass through the document, with jumps occurring only when the appendix is involved. 
  
  All proofs are explained in sufficient detail to avoid having the reader fill in gaps, and all references to previous propositions have hyperlinks, so that you can hover your mouse over them in a PDF reader to view those propositions without jumping to them, allowing your thinking to be contiguous and uninterrupted. Soft explanations are inserted whenever needed, explaining the motivation or structure of a chapter from a high-level perspective, to keep your entire journey motivated. 

  As a beginner, I have experienced the frustration of having to jump between multiple materials, translating notations back and forth, to piece together a single complete picture of the theory. As such, I have made this material as self-contained as possible. It only requires Hartshorne-level algebraic geometry and homological algebra. Furthermore, to achieve maximum self-containment, every proposition in this document containing a concept defined in this document has a proof, as far as I know. 

  Based on my experience with programming, I've spent much time optimizing the division of chapters and sections, arranging my document in such a way that the materials are as modular as possible, highlighting encapsulation and separation of concerns, so that each section internally appears as a collection of involved and detailed proofs and theory development, and externally as a set of clean and intuitive interfaces to be invoked in later sections. 

  I believe that I have arranged my document in a practically superior way. Indeed, I think you may find it encouraging that a friend of mine—then a fourth-year undergraduate who had once been interested in algebraic geometry but had been specializing in statistics for more than two years—successfully understood the computation of etale cohomology of curves using this material with my explanation in an hour.
]

#let epilogue = [
  Since you have reached this point, I have to congratulate you on learning every ingredient you will need to understand the proof of the Weil conjectures. 

  Now this section is going to be much more personal than all other sections in this document, most of them being dense maths. I'll talk a bit about my story with algebraic geometry. Hopefully this is a good story, and it is going to encourage you. 

  My first attempt at algebraic geometry started in the summer of 2022, when one of my teaching assistants arranged an algebraic geometry seminar. He gathered some 20 freshmen and planned to cover Chapters 2 and 3 of @cite-hartshorne-ag in a series of around 10 talks. As you can imagine, most of us couldn't follow it. At that time, category theory was alien to me, consisting of unreasonably large objects in which set-theoretic difficulties may hide. Categories are large, functors are larger, and everything is unfamiliar. I eventually stopped following when they introduced derived functors. They are families of functors constructed from non-canonical injective resolutions, whose well-definedness and functoriality follow from technical lemmas in homological algebra. It was too much for me to accept all at once. 

  After that, I became very scared of algebra, and focused on learning analysis for two years. Then in my third year, I learned analytic number theory for the "analytic" part, and the next semester I learned algebraic number theory for the "number theory" part. Then I decided to specialize in analytic number theory. By the end of the third year, I became familiar with the theory of classical analytic number theory, and also the classical theory of modular forms. I became aware of a few things: 
  - The optimal bounds for complete (and some incomplete) algebraic exponential sums, most prominently Kloosterman sums, are obtained through $ell$-adic cohomology; 
  - The optimal bounds for the Ramanujan conjecture for holomorphic modular forms are obtained through $ell$-adic cohomology by embedding modular forms into etale cohomology of Shimura varieties; 
  - Some technical bounds in the proof of bounded prime gaps are obtained through these mechanisms as well. 

  Then at the start of the summer vacation of 2025, I made the decision that, for the purpose of acquiring an extra tool, I was going to leave my comfort zone and learn algebraic geometry and etale cohomology. I have about 10 friends who knew algebraic geometry really well. Also, at that time, the AI model with the highest reputation among my fellows was Gemini, followed closely by DeepSeek. I hadn't purchased Gemini at that time, so I just used DeepSeek. As you have probably observed, I did happen to have superior conditions for learning algebraic geometry. 
  
  I obtained a copy of @cite-hartshorne-ag, and with the help of around 10 friends, and also DeepSeek as a source of answers to quick doubts, I started grinding through Chapters 2 and 3 of @cite-hartshorne-ag whilst compiling exercise solutions with a Typst/Tinymist workflow. 
  
  For a few weeks, I ground through the book with draft sheets and a keyboard essentially all day.#footnote[...and played the visual novel _Summer Pockets_ in the final hour or two of each day for entertainment.] The days were routine, but I could feel the steady progress and the concrete improvement of my understanding and intuition in algebraic geometry. It was definitely a very memorable summer vacation for me. By early November, I had finished Chapters 2 and 3 of the book. 

  Then (with some overlap in the timeline) came the 2025 Fall course by Prof. Koji Shimizu on etale cohomology, which I mentioned in the acknowledgements. My newly obtained algebraic geometric capabilities at that time were definitely not good enough to understand the whole course at the speed of its progression, but I did decide to compile a set of notes for it. 

  The rest of the story has some repetition with the acknowledgements. Many of my friends took the same 2025 Fall course as me, but for the purpose of compiling these notes, it's not like I should have asked them to dive into all kinds of technicalities in place of me. As a result, I mostly got help from textbooks (including @cite-SP, of course) and AI models. The compilation of this document burnt through a substantial portion of my free time for half a year. You can even infer this timespan from the disclosure of AI usage section - it lasted from Gemini 3.1 to ChatGPT 6 Astra (#furi[who?][which] didn't get to participate in this project). 
  
  It really has been an incredible journey for me. Like many mathematicians, I do have some doubts and anxiety about the impact of recent developments in large language models on mathematics. Yet at least in the short term, they have been and will be powerful and pleasant tools. This experience also gave me the idea that it is not only possible, but also practical to step outside one's own comfort zone, especially with AI assistance these days. The hardest part is of course to have enough free time to burn. Other than that, all it takes is probably some courage to make the commitment, and some enthusiasm to drive you through at least the initial part of the project.#footnote[After that, I personally think that sunk costs can partially take over the role of enthusiasm.] Then it boils down to a test of diligence to push the project to the end. 

  I've finished this bittersweet project, and will move on to the next task. You've finished reading this book, and will probably also move on. Hopefully I told a good story, and hopefully you can get a little bit of courage from it, when you need some. 

  You should probably take a long break now, while looking forward to setting sail again. As the Chinese saying goes, "_Do all you can, and accept what fate has ordained._" (尽人事，听天命). While going forward, you are always free to reevaluate your choices and your destination, but try not to let a difficult day decide for you. May you paint your own story with colors of your choice. Good luck, and keep going. #v(0.5em)
  #align(right)[
    Void, 2026/9/8
  ]
]

// #acknowledgements
// #bibliography("references.bib", style: "void-custom-cite.csl")
