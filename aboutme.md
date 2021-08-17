---
layout: about
title: About me
subtitle: [Work In Progress]
---

\documentclass[letterpaper,11pt]{article}

\usepackage{latexsym}
\usepackage[empty]{fullpage}
\usepackage{titlesec}
\usepackage{marvosym}
\usepackage[usenames,dvipsnames]{color}
\usepackage{verbatim}
\usepackage{enumitem}
\usepackage[hidelinks]{hyperref}
\usepackage{fancyhdr}
\usepackage[english]{babel}
\usepackage{tabularx}
\usepackage{fontawesome}
\usepackage{dirtytalk}
\input{glyphtounicode}


%----------FONT OPTIONS----------
% sans-serif
% \usepackage[sfdefault]{FiraSans}
% \usepackage[sfdefault]{roboto}
% \usepackage[sfdefault]{noto-sans}
% \usepackage[default]{sourcesanspro}

% serif
% \usepackage{CormorantGaramond}
% \usepackage{charter}


\pagestyle{fancy}
\fancyhf{} % clear all header and footer fields
\fancyfoot{}
\renewcommand{\headrulewidth}{0pt}
\renewcommand{\footrulewidth}{0pt}

% Adjust margins
\addtolength{\oddsidemargin}{-0.5in}
\addtolength{\evensidemargin}{-0.5in}
\addtolength{\textwidth}{1in}
\addtolength{\topmargin}{-.5in}
\addtolength{\textheight}{1.0in}

\urlstyle{same}

\raggedbottom
\raggedright
\setlength{\tabcolsep}{0in}

% Sections formatting
\titleformat{\section}{
  \vspace{-4pt}\scshape\raggedright\large
}{}{0em}{}[\color{black}\titlerule \vspace{-5pt}]

% Ensure that generate pdf is machine readable/ATS parsable
\pdfgentounicode=1

%-------------------------
% Custom commands
\newcommand{\resumeItem}[1]{
  \item\small{
    {#1 \vspace{-2pt}}
  }
}

\newcommand{\education}[7]{
	\vspace{-2pt}\item
	\begin{tabular*}{0.97\textwidth}[t]{l@{\extracolsep{\fill}}r}
		\textbf{#1} & #2 \\
		\textit{\small#3} & \textit{\small #4} \\
		\textit{\small#5} & \textit{\small #6}\\		
		& \textit{\small#7} \\		
	\end{tabular*}\vspace{-7pt}
}

\newcommand{\education}[5]{
	\vspace{-2pt}\item
	\begin{tabular*}{0.97\textwidth}[t]{l@{\extracolsep{\fill}}r}
		\textbf{#1} & #2 \\
		\textit{\small#3} & \textit{\small #4} \\
		 & \textit{\small#5} \\		
	\end{tabular*}\vspace{-7pt}
}

\newcommand{\experience}[5]{
	\vspace{-2pt}\item
	\begin{tabular*}{0.97\textwidth}[t]{l@{\extracolsep{\fill}}r}
		\textbf{#1} & #2 \\
		\textit{\small#3} & \textit{\small #4} \\
		\textit{\small#5}\\		
	\end{tabular*}\vspace{-7pt}
}

\newcommand{\resumeSubheading}[4]{
  \vspace{-2pt}\item
    \begin{tabular*}{0.97\textwidth}[t]{l@{\extracolsep{\fill}}r}
      \textbf{#1} & #2 \\
      \textit{\small#3} & \textit{\small #4} \\
    \end{tabular*}\vspace{-7pt}
}

\newcommand{\resumeSubSubheading}[2]{
    \item
    \begin{tabular*}{0.97\textwidth}{l@{\extracolsep{\fill}}r}
      \textit{\small#1} & \textit{\small #2} \\
    \end{tabular*}\vspace{-7pt}
}

\newcommand{\resumeProjectHeading}[2]{
    \item
    \begin{tabular*}{0.97\textwidth}{l@{\extracolsep{\fill}}r}
      \small#1 & #2 \\
    \end{tabular*}\vspace{-7pt}
}

\newcommand{\papers}[1]{
	\item #1
	\vspace{-7pt}
}

\newcommand{\resumeSubItem}[1]{\resumeItem{#1}\vspace{-4pt}}

\renewcommand\labelitemii{$\vcenter{\hbox{\tiny$\bullet$}}$}

\newcommand{\resumeSubHeadingListStart}{\begin{itemize}[leftmargin=0.15in, label={}]}
\newcommand{\resumeSubHeadingListEnd}{\end{itemize}}
\newcommand{\resumeItemListStart}{\begin{itemize}}
\newcommand{\resumeItemListEnd}{\end{itemize}\vspace{-5pt}}
\newcommand{\colorHref}[3][blue]{\href{#2}{\color{#1}{#3}}}
%-------------------------------------------
%%%%%%  RESUME STARTS HERE  %%%%%%%%%%%%%%%%%%%%%%%%%%%%


\begin{document}


\begin{center}
    \textbf{\Huge \scshape Amitayush Thakur} \\ \vspace{1pt}
    \faPhone \quad \small +91-7737485224 $|$ 
    \faMailForward \quad \colorHref{mailto:amitayusht@gmail.com}{\underline{amitayusht@gmail.com}} $|$ 
    \faLinkedin \quad \colorHref{https://linkedin.com/in/amitayush-thakur}{\underline{in/amitayush-thakur}} $|$
    \faGithub \quad \colorHref{https://github.com/amit9oct}{\underline{amit9oct}} $|$
    \faGlobe \quad \colorHref{https://amit9oct.github.io}{\underline{amit9oct.github.io}}    
\end{center}


%-----------EDUCATION-----------
\section{Education}
  \resumeSubHeadingListStart
    \education
      {Birla Institute Of Technology and Science, Pilani}{Pilani, India}
      {Master of Science (Hons.) Mathematics}{Aug. 2012 -- July 2017}
      {Bachelor of Engineering (Hons.) Computer Science}{Aug. 2012 -- July 2017}      
      {Cumm. GPA - 9.02/10}
  \resumeSubHeadingListEnd


%-----------EXPERIENCE-----------
\section{Experience}
  \resumeSubHeadingListStart
    \experience
      {Software Engineer II}{September 2019 -- Present}
      {Microsoft India Development Center}{Hyderabad, India}
      {Microsoft Azure Backup (MAB) team}
      \resumeItemListStart
        \resumeItem{Developed technique for unsupervised pattern mining of service trace logs to predict root cause for the customer issues. The method was based on clustering similar logs and then training a decision tree on top of it to infer the reasoning behind the clustering. This inference was then used by service engineers to figure out the root cause for the customer issues. Mentored interns to implement the same.}      
        \resumeItem{Developed \& Designed a standalone micro-service to efficiently back up hierarchies of objects, such as File Shares, on Cloud. The micro-service split the entire backup into multiple smaller disjoint sub-tasks and then efficiently solved these sub-tasks in parallel---the idea was inspired from map reduce. Designed algorithms, along with proof of correctness, to figure out differences between two hierarchies of objects facilitating incremental backups i.e. only backing up the changed objects}
      \resumeItemListEnd

    \experience
      {Software Engineer}{July 2017 - August 2019}
      {Microsoft India Development Center}{Hyderabad, India}
      {Microsoft Azure Backup (MAB) team}
      \resumeItemListStart
        \resumeItem{Focused on creating micro-services, distributed systems, using formal methods (TLA+), unit testing, scaling, Azure Cloud Storage, File Systems}
        \resumeItem{Developed and Designed Scalable \& Distributed Billing orchestrator for Azure Backup. The overall time to compute billing related information improved \textbf{6x} because of the distributed design.}
    \resumeItemListEnd
     
    \resumeSubheading
      {Research Intern}{Jan 2017 - June 2017}
	  {Microsoft Research}{Bangalore, India}
      \resumeItemListStart
        \resumeItem{Worked on Program Synthesis with Microsoft's \emph{PROSE (Program Synthesis using Examples) SDK} team. Work was related to use of ML in PL}
        \resumeItem{It involved synthesizing programs which were generated on a restricted grammar using input-output examples, and then using ML to rank generated programs to get the most useful program.}
      \resumeItemListEnd
      
    \experience
		{Software Engineering Intern}{May 2016 - July 2016}
		{Microsoft India Development Center}{Hyderabad, India}
        {Microsoft Azure Backup (MAB) team}
		\resumeItemListStart
		\resumeItem{Improved performance for recovering parts of data from large ($\ge$ 1 TB) backed-up disks, the performance went up from \textbf{10 hrs to 3 mins} using iSCSI and mocking certain layers of NTFS file system.}
		\resumeItemListEnd
		
    \resumeSubheading
		{Summer Research Fellow}{May 2015 - July 2015}
		{National Institute of Science Education \& Research}{Bhubaneswar, India}
		\resumeItemListStart
		\resumeItem{Worked under Professor Brundaban Sahu in Computational Number Theory}
		\resumeItem{The main focus was studying the time complexity of Lenstra's Elliptic Curve Factorization Algorithm, and its relation to y-smooth numbers}
		\resumeItemListEnd
	
    \resumeSubheading
		{Project Trainee}{May 2014 - July 2014}
		{Bhabha Atomic Research Centre ( BARC )}{Mumbai, India}
		\resumeItemListStart
		\resumeItem{Worked in development of Network Management System and automation modules.}
		\resumeItemListEnd	

  \resumeSubHeadingListEnd

\section{Publications}
\resumeSubHeadingListStart
	\papers{A. Gautam, A. Thakur, G. Dhanania and S. Mohan, \textbf{\textit{\say{A distributed algorithm for balanced multi-robot task allocation,}}} 2016 11th International Conference on Industrial and Information Systems (ICIIS), Roorkee, 2016, pp. 622-627, doi: 10.1109/ICIINFS.2016.8263014.} [\colorHref{https://ieeexplore.ieee.org/document/8263014}{IEEE Link}]		
\resumeSubHeadingListEnd


\section{Research Interests}
\resumeSubHeadingListStart
\papers{\textbf{Primary Interests:} Theoretical Machine Learning, NLP, Robotics, AI, Theory Of Computation, Compilers, Distributed Systems}
\papers{\textbf{Other Interests:} Cryptography, Number Theory, Quantum Physics}		
\resumeSubHeadingListEnd

%-----------PROJECTS-----------
\section{Projects}
    \resumeSubHeadingListStart
      \resumeProjectHeading
		{\textbf{TUTOR: Text to qUery generaTOR} $|$ \emph{SQL query synthesis from Natural Language}}{\colorHref{https://github.com/amit9oct/Program-Synthesizer}{Github Link}}
			\resumeItemListStart
				\resumeItem{TUTOR is a library to generate simple SQL query from natural language (English). Written In Python. It uses NLP tools (spaCy) to find out the entities present in the query, understand the PoS and dependency tree of the text query.}
				\resumeItem{It applies heuristics to summarize the Natural
					Language Query as an Abstract Meaning Representation (AMR) Tree which captures the semantic meaning of the query. It then uses this AMR and tries to create a valid Abstract Syntax Tree (AST) from it. After this a code generator runs over the AST	and generates the SQL query using CFG (context free grammar) for SQL. This idea works good for simple queries.}
			\resumeItemListEnd
    
      \resumeProjectHeading
          {\textbf{Say No To SQL} $|$ \emph{SQL query synthesis from Input-Output examples}}{\colorHref{https://github.com/amit9oct/SayNoToSQL}{Github Link}}
          \resumeItemListStart
            \resumeItem{In C\#. Takes csv based input and output tables as examples and synthesizes SQL query.}
            \resumeItem{It uses Microsoft’s \colorHref{https://www.microsoft.com/en-us/research/group/prose/}{PROSE} SDK}
          \resumeItemListEnd
 
       \resumeProjectHeading
			 {\textbf{Toy Compiler} $|$ \emph{Compiler \& Runtime Env built for pedagogical purpose}}{\colorHref{https://github.com/amit9oct/Toy-Compiler}{Github Link}}
			 \resumeItemListStart
				 \resumeItem{Toy-Compiler can be used for educational purpose. Helpful for those who need to design a compiler for a simple language. It has the complete compiler built in C language which includes lexer, parser and code generator built without using any libraries like Lex / Yacc}
			 \resumeItemListEnd
 
          
    \resumeSubHeadingListEnd


%-----------PROGRAMMING SKILLS-----------
\section{Other Technical Skills}
 \begin{itemize}[leftmargin=0.15in, label={}]
    \small{\item{
     \textbf{Technologies}{: Git, Docker, Microsoft Azure Cloud, Distributed Systems, Map Reduce, Micro-Service Architecture, App Development, Web Development, Formal Methods (TLA+)} \\
     \textbf{Languages}{: C\#, Python, Java, C/C++, JavaScript} \\     
     \textbf{Libraries}{: scikit-learn, pandas, NumPy, Matplotlib, spaCy}\\
     \textbf{Others}{: LaTeX} \\     
    }}
 \end{itemize}

\section{Achievements}
\begin{itemize}[leftmargin=0.15in, label={}]
	\small{\item{
			\textbf{2019}{: Microsoft Azure Backup Star Award for Innovation} \\				
			\textbf{2019}{: Top 1.4\% (among 100,000 students) in GATE 2019} \\			
			\textbf{2015}{: Indian National Academy Of Science Summer Research Fellowship for Mathematics} \\		
			\textbf{2014}{: Course Topper in Number Theory} \\
			\textbf{2013-14}{: Awarded Merit Scholarship at BITS Pilani for 3 semesters} \\
			\textbf{2013}{: Course Topper in Discrete Mathematics} \\			
			\textbf{2013}{: Qualified for 2013 ACM-ICPC Asia Amritapuri Regional, Team Name: Param Name} \\	
			\textbf{2012}{: Top 2\% (among 500,000 students) in IIT-JEE 2012} \\    
	}}
\end{itemize}

%--REFs---
% IIT Results 2012: https://captnemo.in/projects/iitjee/2012.html
% IIT 2012 percentile: https://economictimes.indiatimes.com/industry/services/education/iit-jee-2012-results-declared-in-the-capital-on-friday/articleshow/13267124.cms?from=mdr#:~:text=G%20B%20Reddy%20said.-,A%20total%20of%209%2C647%20seats%20are%20available%20across%20the%2017,for%20IIT%2DJEE%20this%20year.

%-------------------------------------------
\end{document}