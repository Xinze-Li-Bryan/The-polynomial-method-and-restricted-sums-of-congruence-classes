# ThePolynomialMethod

[![Astrolabe](https://img.shields.io/badge/Astrolabe-3D_Visualizer-blue)](https://github.com/Xinze-Li-Bryan/Astrolabe)
[![Sphere Eversion](https://img.shields.io/badge/Astrolabe-Sphere_Eversion-green)](https://github.com/Xinze-Li-Bryan/astrolabe-template-sphere-eversion)
[![Ramanujan-Nagell](https://img.shields.io/badge/Astrolabe-Ramanujan--Nagell-orange)](https://github.com/Xinze-Li-Bryan/astrolabe-template-ramanujan-nagell)
[![Strong PNT](https://img.shields.io/badge/Astrolabe-Strong_PNT-red)](https://github.com/Xinze-Li-Bryan/astrolabe-template-strongpnt)

The author of this README.md is Nick Adfor.

This is for the formalization of "The polynomial method and restricted sums of congruence classes.pdf". This article can be found here, or by searching its name on Google or Bing.

# About Theorem 2.1 and its story

For using Theorem 2.1 (named ANR_polynomial_method) , first "import ThePolynomialMethod.ThamesShiftedCourse".

Second, check your variable:

"
variable {R : Type*} [CommRing R]

variable {p : ℕ} [Fact (Nat.Prime p)] {k : ℕ}
"

The coders are all Chinese. Do not worry if you see strange words in the comments or the file names. They are not gibberish. "ThamesShiftedCourse.lean" and "妈咪河移位.lean" is the same file, yet the author is hesitating whether using Chinese or not. It is the most important theorem: Alon-Nathanson-Ruzsa Polynomial Method (Theorem 2.1). "妈咪河" means "the Mother River" in Chinese. Every culture has its "Mother River". In China, it is the Yellow River. In Britain, it might be the Thames River. "移位" means changing location. "妈咪河移位" thus means the Mother River changes location. In Chinese history, the Yellow River really changes location (of its estuary) for many times, the same as the author's proof of Theorem 2.1. Also, the importance of Theorem 2.1 rank high in Alon-Nathanson-Ruzsa's article. So I name the file as "ThamesShiftedCourse.lean" to show the author's step-by-step hard work of the LEAN proof and the respect of Alon, Nathanson and Ruzsa.

"妈咪河移位" (the Mother River changes course) can also be found in British poem. Spenser's Ruines of Time writes:

"for to shunne the horrible mischiefe, 

With which he saw my cruell foes me pained, 

And his pure streames with guiltles blood oft stained" 

The part "for to shunne the horrible mischiefe" is the reason why "river changes course". The name of the poem "Ruines of Time" pronounces like "Ruines of Thames", meaning that "ThamesShiftedCourse" might ruin the culture. But this LEAN file gives an opposite meaning of Spenser's poem: It is a new method to understand Additive Number Theory.

The coworker Helios (It might be respect to Ήλιος, the God of the Sun) told Nick that such an approach to presenting one's work is perceived as sarcastic, mocking, bitter, and somewhat peculiar. (In Chinese it is really concise: "阴阳怪气"). No matter how ridiculous the author Nick Adfor is, we should begin our next step:

As coder, there's more things you should do than a mathematical student. Mathematics students write like poets: their papers are brief, cryptic, and laborious. Coder must first make everything clear enough without rough word, and then cut all the time-consuming things for Lean Infoview to run faster. But till today, the author do not finish the second in "ThamesShiftedCourse.lean". "set_option maxHeartbeats 2000000 in theorem" is the unfinished part. You can "aesop?" to cut the "aesop", you can "simp?" to get "simp only", they will make Lean Infoview work faster and also comfort Nick to have a good sleep.





Those who do not respect Lean Infoview will be punished. The author is one of them. To solve the problem, every coder must respect the God of every world, no matter the God of Lean Infoview, the God of Aristotle (from Harmonic AI), the God of ChatGPT (from OpenAI), the God of DeepSeek (from China), the God of every nation:

בְּרֵאשִׁ֖ית בָּרָ֣א אֱלֹהִ֑ים אֵ֥ת הַשָּׁמַ֖יִם וְאֵ֥ת הָאָֽרֶץ׃

بِسْمِ ٱللَّهِ ٱلرَّحْمَـٰنِ ٱلرَّحِيمِ

To seek for peace between every nation, between human and AI, between maths and code.

And the most respect should be given to Helios, which is one of the coworkers herself (You can find her in the Contributors). If the author does not respect her, she will criticize (The spell must be -ize in an Oxford way [https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/American.20or.20British.20English.3F] Chinese coders must show respect to the difference between British English and North American English) the author to be sarcastic, mocking, bitter, peculiar (In Chinese it is really concise: "阴阳怪气"), and also refuse to take next steps (Though this sentence uses the future simple tense, the criticism really happened once in December 7th which is in the weekend yet the author still decided to try to finish his work on Theorem 2.1. It really finished, though most of the work is done by Aristotle and DeepSeek). Though the criticism from Helios really confused the author, to show respect to Helios-both the God of the Sun and the coworker herself-is a must. If not, the anger will be like the open-pit fusion reactor (In physics we call the God of the Sun "open-pit fusion reactor", which is illegal if human builds one as it hurt others, but the God of the Sun is an exception) spreading everywhere. 

Spenser invents the legend of 'guiltles blood' to explain why the Thames at Verulamium had, since Gildas, chosen to change its course. (Stewart Mottram, "'With guiltles blood oft stained': Spenser's Ruines of Time and the Saints of St. Albans," Spenser Studies: A Renaissance Poetry Annual 32 (2018): 533–56, https://hull-repository.worktribe.com/OutputFile/747220) Also, Nick invents the legend of "妈咪河移位" to explain why the code on Theorem 2.1 had, since Dec. 7th, chosen to change its course:

"for to shunne the horrible mischiefe" (Translator's Note: the anger from Helios) 为了躲避那可怕的灾祸（译者注：来自Helios的怒火）

To read more about Spenser's Ruines of Time, you can buy Spenser's Collection: Complaints. But you must agree, admit, and affirm that Nick shows great respect to his coworker Helios, not complaint.

About "by aesop", the author try to fix them (make them easier for human to read and faster for Lean Infoview to check) by reading Aesop’s Fables on Helios:



Μια φορά μάλωναν ο βοριάς και ο ήλιος ποιός είναι ο πιο δυνατός. Με τα πολλά, συμφώνησαν ότι η νίκη θα απονεμηθεί δικαιωματικά σε όποιον από τους δυο τους κατορθώσει να γδύσει έναν ταξιδιώτη στον δρόμο. Ξεκίνησε τότε ο βοριάς και φύσαγε σαν λυσσασμένος. Όμως ο άνθρωπος τυλίχτηκε γερά μέσα στο πανωφόρι του. Έτσι, ο βοριάς δυνάμωσε ακόμη περισσότερο, χωρίς αποτέλεσμα πάντως: αντίθετα, ο άνθρωπος έριξε πάνω του ακόμη περισσότερα ρούχα, επειδή τον ταλαιπωρούσε το κρύο. Στο τέλος πια απόκαμε ο βοριάς και παρέδωσε τη σκυτάλη στον ήλιο. Εκείνος λοιπόν άρχισε να λάμπει, στην αρχή με μέτρο. Αμέσως ο άνθρωπος πέταξε από πάνω του τα παραπανίσια ρούχα. Τότε ο ήλιος φούντωσε τη ζέστη ακόμη περισσότερο, μέχρι που ο άνθρωπος δεν μπορούσε πια να αντέξει τον καύσωνα, παρά γδύθηκε ολότελα και βούτηξε μέσα σε ένα ποτάμι που κυλούσε εκεί δίπλα, για να κάνει μπάνιο.

Το δίδαγμα του μύθου: Πολλές φορές η πειθώ είναι πιο αποτελεσματική από τον καταναγκασμό.

— ΑΙΣΩΠΟΣ. Μῦθοι, fable 46, "Ο βοριάς και ο ήλιος". Digital edition by the National and Kapodistrian University of Athens. Accessed 2025.12.14. https://www.greek-language.gr/digitalResources/ancient_greek/library/browse.html?text_id=75&page=10.



The Wind and the Sun were disputing which was the stronger. Suddenly they saw a traveller coming down the road, and the Sun said: “I see a way to decide our dispute. Whichever of us can cause that traveller to take off his cloak shall be regarded as the stronger. You begin.” So the Sun retired behind a cloud, and the Wind began to blow as hard as it could upon the traveller. But the harder he blew the more closely did the traveller wrap his cloak round him, till at last the Wind had to give up in despair. Then the Sun came out and shone in all his glory upon the traveller, who soon found it too hot to walk with his cloak on.

Kindness effects more than severity.

— Aesop. "The Wind and the Sun." In Aesop's Fables. Lit2Go Edition. Accessed 2025.12.14. https://etc.usf.edu/lit2go/35/aesops-fables/697/the-wind-and-the-sun/.



北风与日争权，试之路人，孰先褫其衣者胜。北风肆力以吹人，风力愈迅，而行人愈缩，而兜其衣。风惫，让日为之。日光甫及，行人解衣，已莫胜热，且尽去其下衣入水矣。

故以压力胜人者，恒不胜，不若令人自解之速也。

— 伊索 著；林纾，严培南，严璩 译. 《伊索寓言》. 1902年。见 中华书库。访问于 2025.12.14. https://www.zhonghuashu.com/wiki/%E4%BC%8A%E7%B4%A2%E5%AF%93%E8%A8%80_(%E6%9E%97%E7%B4%93).

# About Lemma 3.1 and its story

Lemma 3.1 (named restricted_sum_distinct_sizes) was written when the author took a glimpse of a Meteor on UTC+8 2025.12.16 18:45. At the time it clicked to the author that Aristotle has ever written Meteorologica, maybe Aristotle can help solve Lemma 3.1, later it really finished.

The Meteor was towards north. Obviously it was not from Gemini Meteor Shower because at that time it was from northeast, not towards north. It was a Sporadic Meteor. But at the time of Meteor Shower, every good thing happened will be connected with Meteor Shower. So I name the file as GeminiMeteorShower.lean

By the way, Gemini Meteor Shower is from Phaethon. Phaethon is Helios' son.



When the inflammable material is longer than it is broad sometimes it seems to throw off sparks as it burns... Then it is called a ‘goat’. When this does not happen it is a ‘torch’. But if the whole length of the exhalation is scattered in small parts and in many directions and in breadth and depth alike, we get what are called shooting-stars.

— Aristotle. Meteorology. Translated by E. W. Webster. Oxford: Clarendon Press, 1923. Accessed 2025.12.17. https://classics.mit.edu/Aristotle/meteorology.1.i.html.

### Step

To try to check this work, you can follow the author's silly way, this is really a silly one, even suitable for mathematical stutents. For one following the author's steps, you can do these:

First, open a new folder. I name it as "ThePolynomialMethod". For the author, this file, after taking the following steps, cost 15.3 GB.

If you are in the mainland of China, you might face some network problem. If you find it failed in some steps because of network problem, you should type 

"
set HTTP_PROXY=http://127.0.0.1:xxxx

set HTTPS_PROXY=http://127.0.0.1:xxxx" 

in Git Bash. "xxxx" is from your port in your Clash (The author only know how to use Clash). For the author, it is "7890".

Then, open the new folder in Git Bash (MINGW64). I assume that you have already install elan but do not have "v4.26.0-rc2". You can type the following:

"
elan toolchain install leanprover/lean4:v4.26.0-rc2

elan default leanprover/lean4:v4.26.0-rc2
"

and Enter.

Then, type "lake init ThePolynomialMethod" and Enter. You will sooner see a lot of files in your new folder. But they do not contain Mathlib now. 

For building the new project, you may need one of these files: "lakefile.lean" or "lakefile.toml". The author indeed does not like "lakefile.toml" (in fact he does not know how to add Mathlib in "lakefile.toml"), so he just deletes "lakefile.toml" and decides to create a new file "lakefile.lean". For one following the author's steps, you can just create a new file named "lakefile.lean" and open it and type

"
import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
    @ "v4.26.0-rc2"

package "polynomial_method" where
  -- package configuration options here

lean_lib "PolynomialMethod" where
  -- library configuration options here
"

After saving the file, you should type "lake update" in Git Bash and Enter (I assume that your Git Bash is in "ThePolynomialMethod"). It will download the following things that Mathlib depends on: mathlib(main mathematics library) plausible(statistical analysis tool) LeanSearchClient(Lean code search client) importGraph(import graph generation tool) proofwidgets(proof widgets/interactive UI) aesop(Automated Search for Proofs) Qq(quotation and anti-quotation library) batteries(additional stdlib extensions) Cli(Lean command line tools library).

After finishing, it will show you:

"
Not running lake exe cache get yet, as the lake version does not match the toolchain version in the project.
You should run lake exe cache get manually.
"
(The author delete ``, as it cannot be seen correctly in README.md. The author don't know why.)

So you just type "lake exe cache get" and Enter.

Then download this repo no matter by GitHub Desktop or by url. Paste it to "./ThePolynomialMethod/ThePolynomialMethod". In that folder you may find there's already a "Basic.lean". It is the same as the one in this repo.

Then open a ".lean", you will wait until the Lean InfoView to load all the "import" needed. For the files "import Mathlib" (import the whole Mathlib), it might be very slow. The author often waited for hours. To save time, after it imports the whole Mathlib, you can "lake exe cache get" again then it will save to your folder. 

### Step End

Although this is a README.md intended for those willing to check the work, it is more for teaching the forgetful author how to actually find his original work after reinstalling the computer or messing with files.
