#import "void-import.typ": *
// #show: void-style

#let acknowledgements = [
  我衷心感谢 Koji Shimizu 教授，他于 2025 年秋季在清华大学开设了平展上同调课程。本书基于他的课程编写。我对这一平易近人的入门讲解十分感激。

  我也衷心感谢平展上同调领域已有的大量通俗参考文献的作者。若没有参阅这些材料并比较其处理方式，我无法把通往平展上同调的道路梳理得清晰、有概念性。这些文献是：Stacks Project @cite-SP、扶磊 @cite-lei-fu、Freitag–Kiehl @cite-freitag-kiehl、Deligne 的 Arcata 笔记 @cite-deligne-arcata、Milne @cite-milne-lectures 与 @cite-milne-etale，当然还有 SGA 原书 @cite-SGA1、@cite-SGA4 与 @cite-SGA4half。

  我还要感谢我的朋友们，他们在本书写作过程中给予我持续的支持、有益的讨论和建议。我的朋友 Irisu（`Irisu7777h@gmail.com`）帮助我对一些大定理（光滑基变换以及 Weil 猜想的框架）建立了高层次的理解，并指出了多处我应留意的技术细节（例如 @chapter-etale-sheaves 中的一处）。#if (not compile-cfg.cover-pic.censored) [他还慷慨地为封面创作了美丽的插图。 ]我的朋友 Sean（#link("https://triangulated-ruler.github.io/index.html", text(fill: blue.darken(25%))[个人主页])）检查了我在 @sect-topological-invariance 中对拓扑不变性的独立证明，并和我讨论了 @chapter-lower-shriek 中的相容性条件。我的朋友兼室友 Darpaz 忍受了我许多个夜晚敲键盘的噪音，还执行了我半夜 0 点突发奇想的点外卖建议。我的朋友 Mark、AppoloniusSun（#link("https://apolloniussun.github.io/", text(fill: blue.darken(25%))[个人主页])）、VByed7（#link("https://vbyed7.github.io/VByed7/", text(fill: blue.darken(25%))[个人主页])）、KahlerManifold 和 SimplicialCat（#link("https://simplicialcat.github.io/", text(fill: blue.darken(25%))[个人主页])）多次听我跟随本书采用的证明路线讲解各种主题，这为我检验自己的理解以及这些路线的有效性提供了宝贵机会。#footnote[这些名字都是化名，因为我默认不公开朋友们的身份。]

  最后同样重要的是，我使用的 AI 模型在本文的构建中发挥了关键作用。我将在“AI 使用披露”一节讨论它们的作用。它们回答了我随手提出的、对人类回答者来说可能过于无趣、技术性或重复的问题。它们也帮助我完善理解，并做了大量艰苦工作。例如，ChatGPT 5.6 Terra 在本文中找出了 996 个笔误，我接受了 956 个，拒绝了 40 个。DeepSeek V4.1 Flash 1017 翻译了全部的正文，光文本就有 1MB。没有 AI 协助，我实在无法想象一位作者如何能完成这样的工程。
]

#let disclosure-of-ai-usage = [
  本书英文原版在以下 AI 模型的协助下完成：ChatGPT 5.6 Sol、ChatGPT 5.6 Terra、ChatGPT 5.5、Gemini 3.1、DeepSeek V4 Pro。

  关于它们的作用，我请它们帮助我理解许多证明背后的想法，也请它们解释我不理解的证明细节。我还让它们承担一些艰苦工作，例如查找并更正笔误、找出需要留意的草率段落，以及为可疑段落和待办事项提出解决方案。

  尽管如此，本书英文原版的 99% 的文字是我自己输入的；AI 模型提出的少数文本块，我都逐块人工核对过。我在此声明：据我所知，本文由我本人能够认同的可靠数学内容构成，不含 AI 幻觉。

  本书的中文版主体由 DeepSeek V4.1 Flash 1017 翻译完成，共消耗约 22 亿 token。我把关了主要的翻译步骤，审核了近千处语言表述上的修改，并对译文进行了几个章节的人工抽检。我认为译文符合中文的语言习惯，是相对流畅、自然的。
]

#let preface = [
  本文最初是 2025 年秋季 Koji Shimizu 教授课程的讲义，致谢中已提到。随着时间推移，我以原始讲义为骨架，重写了大部分内容，并用自己的话加以扩展，以至于它应当被视为我本人的原创作品。

  这份材料特别适合“速通”平展上同调理论，即使读者没有很强的代数几何背景或热情。书名 _平展上同调（Any%）_ 也是出于这个目的：其中“(Any%)”指电子游戏速通的一类规则——只要求尽快完成游戏的主要目标，而不追求 100% 完成度。

  现在你可能会问：本文长达 500 多页，这怎么能叫速通？

  就我个人而言，我相信对于低于某个较大阈值的数学文本，篇幅会带来清晰，而压缩则伴随晦涩。我安排本文的方式是：读者只需按顺序通读一遍，就能对平展上同调获得足够好的理解；只有涉及附录时才需要跳跃。

  所有证明都解释得足够详细，以免读者自行填补空缺；所有对前文命题的引用都带有超链接，你可以在 PDF 阅读器中把鼠标悬停其上查看那些命题，而不必跳转过去，从而让思路保持连贯、不被打断。需要时我会插入一些“软性”说明，从高层次解释一章的动机或结构，让你整个旅程都有动力。

  作为一个初学者，我曾体会过在多种材料之间跳来跳去、反复翻译记号、才能拼出一幅完整理论图景的挫败感。因此，我尽可能让这份材料自足。它只需要 Hartshorne 水平的代数几何与同调代数。此外，为了实现最大程度的自足，据我所知，本文中每个包含本文所定义概念的命题都有证明。

  基于我的编程经验，我花了很多时间优化章节划分，让材料尽可能模块化，强调封装、强调关注点分离：每一节内部看起来都是一组深入而详细的证明与理论展开，外部则是一组干净、直观、可供后续章节调用的接口。

  我相信我的安排在实践中是更优的。事实上，我的一位朋友——他当时是本科四年级，曾经对代数几何感兴趣，但已在统计方向专攻两年多——在我的讲解下，用一小时就成功理解了利用这份材料计算曲线平展上同调的过程；我想这会对你是种鼓励。
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
