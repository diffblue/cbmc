%% ceurart.cls
%% Copyright 2019--2024 CEUR Workshop Proceedings (CEUR-WS.org)
%
% This work may be distributed and/or modified under the
% conditions of the LaTeX Project Public License, either version 1.3
% of this license or (at your option) any later version.
% The latest version of this license is in
%   http://www.latex-project.org/lppl.txt
% and version 1.3 or later is part of all distributions of LaTeX
% version 2005/12/01 or later.
%
% This work has the LPPL maintenance status `maintained'.
%
% The Current Maintainer of this work is Dmitry S. Kulyabov.
% The code was originally based on 'CAS Bundle' code.
%

\def\RCSfile{ceurart}%
\def\RCSversion{0.5.3}%
\def\RCSdate{2024-12-18}%
\RequirePackage{expl3}
\ProvidesExplClass
{\RCSfile} % Package name
{\RCSdate} % Release date
{\RCSversion} % Release version
{Typesetting articles for CEUR Workshop Proceedings (CEUR-WS.org)} % Description

\RequirePackage{xparse}
\@ifundefined{regex_match:nnTF}{\RequirePackage{l3regex}}{}

\ExplSyntaxOn

%%
%% switches
%%

\newif\iflongmktitle    \longmktitlefalse

%% twocolumn
\newif\ifdc             \global\dcfalse
\newif\ifsc             \global\sctrue
\newif\ifcasreviewlayout  \global\casreviewlayoutfalse
\newif\ifcasfinallayout   \global\casfinallayoutfalse
%% enable header and footer
\bool_new:N \g_ceur_hf_bool
\bool_gset_false:N \g_ceur_hf_bool

% \ifhf
%   \bool_gset_true:N \g_ceur_hf_bool
% \fi
%% header and footer
% \newif\ifhf
% \global\hffalse

\newcounter{blind}
\setcounter{blind}{0}

% \def\blstr#1{\gdef\@blstr{#1}}
% \def\@blstr{1}
% \newdimen\@bls
% \@bls=\baselineskip

%\newif\if@twocolumn
\DeclareOption{twocolumn}{\global\dctrue \global\scfalse}
\DeclareOption{hf}{\bool_gset_true:N \g_ceur_hf_bool}
% \DeclareOption{hf}{\global\hftrue}

\DeclareOption{singleblind}{\setcounter{blind}{1}}
\DeclareOption{doubleblind}{\setcounter{blind}{2}}
\DeclareOption{longmktitle}{\global\longmktitletrue}
\DeclareOption{final}{\global\casfinallayouttrue}
\DeclareOption{review}{\global\casreviewlayouttrue}

% \ExecuteOptions{a4paper,10pt,oneside,review}
% \ExecuteOptions{a4paper,oneside,10pt,DIV=calc}
\DeclareOption*{\PassOptionsToClass{\CurrentOption}{scrartcl}}
\PassOptionsToClass{a4paper,twoside=false}{scrartcl}
\ProcessOptions\relax
\LoadClass{scrartcl}
\KOMAoptions{DIV=10}
\ifdc
  \KOMAoptions{fontsize=9pt}
\else
  \KOMAoptions{fontsize=11pt}
\fi

\RequirePackage{graphicx}
\RequirePackage{amsmath,amsfonts,amssymb}
\allowdisplaybreaks

\RequirePackage{etoolbox,balance}
\RequirePackage{booktabs,makecell,multirow,array,colortbl,dcolumn,stfloats}
\RequirePackage{xspace,xstring}
\RequirePackage[hang,flushmargin]{footmisc}
\RequirePackage[svgnames,dvipsnames]{xcolor}
\RequirePackage{iftex}
\RequirePackage{microtype}

%% PDF/A support

\ifpdftex
\RequirePackage{cmap}
\fi

\bool_new:N \g_ceur_pdfx_bool
\bool_gset_false:N \g_ceur_pdfx_bool

\file_if_exist:nTF { pdfx.sty } {%

  % {{{ Temporary fix for error using pdfx on Tex Live 2021

  % pdfx v1.6.3 from 2019-02-27 is bad, so anything later is hopefully fixed...

  % \IfFormatAtLeastTF do not exist in LaTeX versions older than 2020-10-01.
  \providecommand\IfFormatAtLeastTF{\@ifl@t@r\fmtversion}
  % Problem with issue https://github.com/latex3/latex2e/issues/605
  % We do not need fix with older version of LaTeX
  \IfFormatAtLeastTF{2021/06/01}{%

    % temporarily reverts https://github.com/latex3/latex2e/commit/5fb2860f2fedc87b213730f06ec1d77bcab4814a
    % resp. https://github.com/latex3/latex2e/commit/dd2ec509ec98e9c359a41e35aea6aade86485ca2
    % as it breaks pdfx (see https://tex.stackexchange.com/questions/605854/error-using-pdfx-on-tex-live-2021)

    % this is the old implementation from base/ltpara.dtx, version 1.0g
    \cs_new_protected:Npn \__old_para_end: {
      % ltpara v1.0h as well as firstaid/latex2e-first-aid-for-external-files.dtx v1.0o inserted
      % \scan_stop: here, which breaks pdfx
      \mode_if_horizontal:TF {
        \mode_if_inner:F {
          \tex_unskip:D
          \hook_use:n{para/end}
          \@kernel@after@para@end
          \mode_if_horizontal:TF {
            \if_int_compare:w 0 < \tex_lastnodetype:D
            \tex_kern:D \c_zero_dim
          \fi:
          \tex_par:D
          \hook_use:n{para/after}
          \@kernel@after@para@after }
          { \msg_error:nnnn { hooks }{ para-mode }{end}{horizontal} }
        }
      }
      \tex_par:D
    }

    % \PackageWarning{ceurart}{Patching~\para_end:~implementation~to~fix~pdfx}

    \cs_set_eq:NN \par     \__old_para_end:
    % these two aren't actually required to fix pdfx, so we'll skip them...
    % \cs_set_eq:NN \@@par   \__old_para_end:
    % \cs_set_eq:NN \endgraf \__old_para_end:

    \AtBeginDocument{

      % \PackageWarning{ceurart}{Restoring~old~\para_end:~implementation}

      % restore additional definitions
      \cs_set_eq:NN \par     \para_end:
      % see above: as we didn't replace them, no need to restore them.
      % \cs_set_eq:NN \@@par   \para_end:
      % \cs_set_eq:NN \endgraf \para_end:
    }
  }{}

  % }}}

  \RequirePackage[useBOM,pdf17,a-1a]{pdfx}
  \bool_gset_true:N \g_ceur_pdfx_bool
}{%
  \RequirePackage[unicode]{hyperref}
}
\hypersetup{%
  colorlinks,
  bookmarksnumbered,
  pdfencoding=unicode,
  allcolors=DarkSlateGrey
}
\pdfstringdefDisableCommands{%
  \def\addtocounter#1#2{}%
  \def\unskip{}%
  \def\textbullet{- }%
  \def\textrightarrow{ -> }%
  \def\footnotemark{}%
}
\urlstyle{rm}
\colorlet{scolor}{black}
\colorlet{hscolor}{DarkSlateGrey}
% \AtEndDocument{\hypersetup
%   {pdftitle={\csuse{__short_title:}},
%   pdfauthor={\csuse{__short_authors:}}}}

\let\comma\@empty
\let\tnotesep\@empty
\let\@title\@empty

\let\pdfxauthors\@empty
\let\pdfxkeywords\@empty

%
% Load Common items
%

%%
%%
%%

%%
%% Bools
%%

%%
%% Bells and Whistles
%%

\bool_new:N \g_ceur_nologo_bool
\bool_gset_false:N \g_ceur_nologo_bool

\file_if_exist:nTF { fontawesome5.sty } {%
  \RequirePackage{fontawesome5}
  % We need orcid icon
  \@ifpackagelater{fontawesome5}{2020/01/17}{%
    \bool_gset_false:N \g_ceur_nologo_bool
  }{%
    \bool_gset_true:N \g_ceur_nologo_bool
  }
}{%
  \bool_gset_true:N \g_ceur_nologo_bool
}

%%
%% PDF/A
%%

%% allocate a write stream
\iow_new:N \g_xmpdata_output_iow
\iow_open:Nn \g_xmpdata_output_iow { \c_sys_jobname_str .xmpdata }

%% User interface
\NewDocumentCommand{\xmpdatawrite}{ m m } {
  \xmpdata_write:n { \iow_char:N \\ #1 \iow_char:N \{ #2 \iow_char:N \} }
}

%% Inner function
\cs_new_protected:Npn \xmpdata_write:n #1
{
  \iow_now:Nx \g_xmpdata_output_iow { #1 }
}

%%
%% Utils
%%

%% Workaround for unwanted '.pdf' to path (provided by hyperref)
%% https://tex.stackexchange.com/questions/154335/href-adds-unwanted-pdf-to-path-provided
\providecommand*{\hrefurl}{\hyper@normalise\hrefurl@}
\providecommand*{\hrefurl@}[2]{\hyper@linkurl{#2}{#1}}

%%
%%
%%

% \newcommand\ceurConference[4][]{%
%   \gdef\ceurConference@shortname{#1}%
%   \gdef\ceurConference@name{#2}%
%   \gdef\ceurConference@date{#3}%
%   \gdef\ceurConference@venue{#4}%
%   \ifx\ceurConference@shortname\@empty
%     \gdef\ceurConference@shortname{#2}%
%   \fi
% }

\DeclareRobustCommand\conference[1]{%
  \gdef\ceurConference@name{#1}%
}

\NewDocumentCommand \noindentfoot {} {
  \raggedright
  \hspace*{-\parindent}
  \hspace*{-\footnotemargin}
}

%
% Specific to Single Column
%

\RenewDocumentCommand \maketitle {} {
  \nonumnote{\itshape \ceurConference@name}
  \logonote{\@copyrightLine}
  % \logonote{\@ceurLogoLine} % 2023-23-13/Manfred: The CEUR logo is no longer included via CEURART. Instead, we include it during the watermarking when a paper is actually published
  % \ifbool { usecasgrabsbox }
  %   {
  %     \setcounter{page}{0}
  %     \thispagestyle{empty}
  %     \unvbox\casgrabsbox
  %   } { }
  % \pagebreak
  % \ifbool { usecashlsbox }
  %   {
  %     \setcounter{page}{0}
  %     \thispagestyle{empty}
  %     \unvbox\casauhlbox
  %   } { }
  %     \pagebreak
  \thispagestyle{plain}
  \xdef\firstpage{\thepage}
  % \thispagestyle{first}
  % \pagestyle{standard}
  \ifbool{longmktitle}
  {
    \LongMaketitleBox
    \ProcessLongTitleBox
  }
  {
    \ifbool{dc}
    { \twocolumn[\MaketitleBox] }
    { \MaketitleBox }
    \printFirstPageNotes
  }
  \normalcolor \normalfont
  \setcounter{footnote}{\int_use:N \g_ceur_fnote_int}
  \renewcommand\thefootnote{\arabic{footnote}}
  \gdef\@pdfauthor{\infoauthors}
  % \gdef\@pdfsubject{Complex ~CEUR ~Content}

  %% PDF/A

  % List of supported metadata fields

  % General information:

  % \Author           - the document's human author. Separate multiple authors with \sep.
  % \Title            - the document's title.
  % \Keywords         - list of keywords, separated with \sep.
  % \Subject          - the abstract.
  % \Org              - publishers.

  % Copyright information:

  % \Copyright        - a copyright statement.
  % \CopyrightURL     - location of a web page describing the owner and/or rights statement for this document.
  % \Copyrighted      - 'True' if the document is copyrighted, and
  % 'False' if it isn't. This is automatically set to 'True' if either
  % \Copyright or \CopyrightURL is specified, but can be overridden.

  % Publication information:

  % \PublicationType   - The type of publication. If defined, must be
  % one of book, catalog, feed, journal, magazine,
  % manual, newsletter, pamphlet. This is
  % automatically set to "journal" if \Journaltitle
  % is specified, but can be overridden.
  % \Journaltitle      - The title of the journal in which the document
  % was published.
  % \Journalnumber     - The ISSN for the publication in which the
  % document was published.
  % \Volume            - Journal volume.
  % \Issue             - Journal issue/number.
  % \Firstpage         - First page number of the published version of
  % the document.
  % \Lastpage          - Last page number of the published version of
  % the document.
  % \Doi               - Digital Object Identifier (DOI) for the
  % document, without the leading "doi:".
  % \CoverDisplayDate  - Date on the cover of the journal issue, as a
  % human-readable text string.
  % \CoverDate         - Date on the cover of the journal issue, in a
  % format suitable for storing in a database field
  % with a 'date' data type.

  \bool_if:NTF \g_ceur_pdfx_bool
  {
    \xmpdatawrite{Title}{\detokenize\expandafter{\casprelimstitle}}
    \xmpdatawrite{Author}{\pdfxauthors}
    \xmpdatawrite{Keywords}{\pdfxkeywords}
    \xmpdatawrite{Subject}{Layout~by~CEURART~v\RCSversion}

    \ifx\@copyrightclause\@empty\else
      \xmpdatawrite{Copyright}{\iow_char:N \\ copyright\ \@copyrightyear\ \@copyrightclause}
      \xmpdatawrite{CopyrightURL}{https://creativecommons.org/licenses/by/4.0}
    \fi

    \xmpdatawrite{Journaltitle}{CEUR~Workshop~Proceedings}
    \xmpdatawrite{Journalnumber}{1613-0073}
    \bool_if:NTF \g_ceur_hf_bool {
        \xmpdatawrite{Firstpage}{\firstpage}
        \xmpdatawrite{Lastpage}{\lastpage}
    }{ }
  }{
    \hypersetup{%
      pdfcreator={ceurart.cls},
      % pdfproducer={pdfTeX;},
      % pdftitle={\csuse{__short_title:}},
      % pdfauthor={\csuse{__short_authors:}},
      % pdfauthor={\csuse{__authors:}},
      % pdftitle={\@title},
      pdfsubject={Layout~by~CEURART~v\RCSversion},
      pdfkeywords={\pdfxkeywords},
      linkcolor={hscolor},
      urlcolor={hscolor},
      citecolor={hscolor},
      filecolor={hscolor},
      menucolor={hscolor},
    }
  }
}


  % pdfcreator={ceurart.cls},
  % % pdfproducer={pdfTeX;},
  % % pdftitle={\csuse{__short_title:}},
  % % pdfauthor={\csuse{__short_authors:}},
  % % pdfauthor={\csuse{__authors:}},
  % % pdftitle={\@title},
  % pdfsubject={Layout by CEURART},


%
% Front matter macros
%
% The front matter macros are derived/adopted from stm-prelims.sty
% written by CV Radhakrishnan <cvr@cvr.cc> and copyrighted by him.
% Usage of those macros and methods are gratefully acknowledged.
%

\keys_define:nn { ceur / title } {
  mode      .choice:     ,
  mode / title  .meta:n  = {
    type   = title      ,
    size   = \LARGE      ,
    % size   = \huge      ,
    % shape  = \upshape   ,
    shape  = \sffamily   ,
    % weight = \mdseries  ,
    weight = \bfseries  ,
    color  = black  ,
    before = 0pt        ,
    after  = 0pt        ,
    align  = \raggedright ,
  } ,
  mode / alt  .meta:n  = {
    type   = alt      ,
    size   = \large     ,
    shape  = \upshape   ,
    weight = \mdseries  ,
    color  = black  ,
    before = 6pt        ,
    after  = 0pt        ,
    align  = \raggedright ,
  } ,
  mode / sub    .meta:n  = {
    type   = sub           ,
    size   = \large        ,
    shape  = \upshape      ,
    weight = \mdseries     ,
    color  = black!80  ,
    before = 6pt          ,
    after  = 0pt           ,
    align  = \raggedright  ,
  } ,
  mode / trans   .meta:n  =  {
    type   = trans         ,
    size   = \normalsize   ,
    shape  = \upshape      ,
    weight = \mdseries     ,
    color  = black!60      ,
    before = 6pt           ,
    after  = 0pt           ,
    align  = \raggedright  ,
  } ,
  mode / transsub   .meta:n  = {
    type   = transsub      ,
    size   = \small        ,
    shape  = \upshape      ,
    weight = \mdseries     ,
    color  = black!50      ,
    before = 6pt           ,
    after  = 0pt           ,
    align  = \raggedright  ,
  } ,
  mode / ascii   .meta:n  = {
    type   = ascii            ,
    size   = \small\ttfamily  ,
    shape  = \upshape         ,
    weight = \mdseries        ,
    color  = black            ,
    before = 12pt             ,
    after  = 0pt              ,
    align  = \raggedright     ,
  } ,
  type      .tl_set:N    = \l_ceur_title_type_tl      ,
  size      .tl_set:N    = \l_ceur_title_size_tl      ,
  shape     .tl_set:N    = \l_ceur_title_shape_tl     ,
  weight    .tl_set:N    = \l_ceur_title_weight_tl    ,
  before    .dim_set:N   = \l_ceur_title_before_dim   ,
  after     .dim_set:N   = \l_ceur_title_after_dim    ,
  align     .tl_set:N    = \l_ceur_title_align_tl     ,
  color     .tl_set:N    = \l_ceur_title_color_tl     ,
}

\NewDocumentCommand \processTmarks { } {
  \cs_if_free:cTF { mark@title }
  { \ignorespaces }
  { \tl_set:Nx \l_tmpa_tl { \cs:w mark@title\cs_end: }
    \clist_map_inline:cn { mark@title }
    {
      \str_case:nn { ##1 }
      {
        { 1 }  { $^\star$ }
        { 2 }  { $^{,\star\star}$ }
        { 3 }  { $^{,\star\star\star}$ }
      }
    }
  }
}

\RenewDocumentCommand \title { O{mode = title} m } {
  \pdfstringdef \@pdftitle { #2 }
  \csgdef { casprelimstitle } { #2 }
  \keys_set:nn { ceur / title } { #1 }
  \tl_if_empty:NTF \__short_title: {
    \cs_gset:Nn \__short_title: { #2 }
  }{ }
  \seq_gput_right:Nn \g_ceur_title_seq {
    \keys_set:nn { ceur / title } { #1 }
    % \iow_term:n { MODE:~\l_ceur_title_mode_tl ~ ~ [#1]}
    \par \vskip \l_ceur_title_before_dim
    \l_ceur_title_align_tl
    \l_ceur_title_size_tl
    \l_ceur_title_shape_tl
    \l_ceur_title_weight_tl
    \color { \l_ceur_title_color_tl }
    #2
    \tl_set:Nn \l_tmpa_tl { title }
    \tl_if_eq:NNTF \l_ceur_title_type_tl \l_tmpa_tl
    { \processTmarks } { }
    \par \vskip  \l_ceur_title_after_dim
    \normalcolor \normalsize \normalfont
  }
}

%  \gappto\usestmtitle{#1}%

\renewcommand \@title { \seq_use:Nn \g_ceur_title_seq { } }

\renewcommand{\subtitle}[1]{\title[mode=sub]{#1}}

\NewDocumentCommand \wrAun { m }      %  unexpanded write to aux
   { \iow_now:Nn \@auxout { #1 } }
\NewDocumentCommand \wrAux { m }      %  expanded write to aux
   { \iow_now:Nx \@auxout { #1 } }

\NewDocumentCommand \wrShipAux { m }   % expanded write at shipout
   { \iow_shipout:Nx \@auxout { #1 } }
\NewDocumentCommand \wrShipAun { m }   % unexpanded write at shipout
   { \iow_shipout:Nn \@auxout { #1 } }

\NewDocumentCommand \ceurLabel { m } {
  \@bsphack \wrAux
  { \token_to_str:N \NewLabel { #1 }
    { \@currentlabel }
  } \@esphack
}

\NewDocumentCommand \NewLabel { m m } {
  \cs_if_free:cTF { X@#1: }
  { \cs_new:cx { X@#1: } { #2 } }
  { \cs_set:cx { X@#1: } { #2 } }
}

\NewDocumentCommand \ceurRef { m } {
  \cs_if_free:cTF { X@#1: }
  { 0 } {\use:c {X@#1:} }
}

\seq_clear_new:N \l_fnmk_seq
\NewDocumentCommand \processFnRef { m } {
  \seq_clear:N \l_fnmk_seq
  \clist_map_inline:nn { #1 }
  { \seq_put_right:Nx \l_fnmk_seq
    {\cs_if_free:cTF { X@##1: } {0} { \use:c {X@##1:} }}
  }
}

\NewDocumentCommand \fnmark { O{} } {
  \writemarks { fnau\theau@ } { #1 }
}


\NewDocumentCommand  \fnref { m } {
  \processFnRef { #1 }
  \wrAux { \token_to_str:N \csxdef {mark@fnau\theau@}
    { \seq_use:Nn \l_fnmk_seq  { , } } }
}

\NewDocumentCommand \corref { m } {
  \str_set:Nx \l_tmpa_str { \ceurRef { #1 } }
  \wrAux { \token_to_str:N \csxdef { mark@corau\theau@ }
    {
      \cs_if_free:cTF { X@#1: } {0} { \use:c {X@#1:} }
    }
  }
}

\NewDocumentCommand \cormark { O{} } {
  \@cormarktrue
  \writemarks {corau\theau@} { #1 }
}

\seq_new:N \l_ceur_au_seq
\seq_new:N \l_ceur_au_sn_seq
\seq_new:N \l_ceur_au_fn_seq
\seq_new:N \l_ceur_au_ead_seq
\seq_new:N \l_ceur_au_orcid_seq
\seq_new:N \l_ceur_au_email_seq
\seq_new:N \l_ceur_au_url_seq
\seq_new:N \l_ceur_au_contrib_role_seq

\NewDocumentCommand \parsename { m } {
  \seq_set_split:Nnn \l_ceur_au_seq { ~ } { #1 }
  \seq_pop_right:NN \l_ceur_au_seq \l_ceur_au_sn_seq
  \seq_map_inline:Nn \l_ceur_au_seq
  { \seq_put_right:Nx \l_ceur_au_ead_seq
    { \tl_head:n { #1 }. }
  }
}

\NewDocumentCommand \invparsename { m } {
  \seq_set_split:Nnn \l_ceur_au_seq { ~ } { #1 }
  \seq_pop_left:NN \l_ceur_au_seq \l_ceur_au_sn_seq
  \seq_map_inline:Nn \l_ceur_au_seq
  { \seq_put_right:Nx \l_ceur_au_ead_seq
    { \tl_head:n { #1 }. }
  }
}

\NewDocumentCommand \surname {} {
  \l_ceur_au_sn_seq
}

\NewDocumentCommand \firstname {} {
  \seq_use:Nn \l_ceur_au_seq { \no_break_space: }
}

\NewDocumentCommand \eadauthor {} {
  \seq_map_inline:Nn \l_ceur_au_seq
  {
    \regex_match:nnTF { \. } { ##1 }
    { ##1 \, }
    { \tl_head:n {##1}. \, }
  } {\,} \l_ceur_au_sn_seq
}

\cs_set_eq:NN \shortauthor \eadauthor

\seq_clear_new:N \l_affmk_seq
\NewDocumentCommand \processAffRef { m }
   {
     \seq_clear:N \l_affmk_seq
     \clist_map_inline:nn { #1 }
     {
       \seq_put_right:Nx \l_affmk_seq
       {\ceurRef{##1}}
      }
    }

\NewDocumentCommand \processAffNum { m }
   {
     \seq_clear:N \l_affmk_seq
     \clist_map_inline:nn { #1 }
     {
       \seq_put_right:Nn \l_affmk_seq
       { \int_to_arabic:n {##1} }
      }
    }

\NewDocumentCommand \listAff { }
   {
     \tl_if_blank:nTF { \l_affmk_seq }
       { \tl_gset:Nn \g_ceur_comma_tl { 0 } }
       {
         \seq_use:Nn \l_affmk_seq { , }
         \tex_def:D \sep{\unskip,}
       }
   }

\NewDocumentCommand \ead { O{} m }
   {
     \tl_if_empty:nTF { #1 } { \@ead {#2} } { \@uad[#1]{#2} }
   }

\NewDocumentCommand \eadsep { } { }

\int_new:N \g_ead_int
\seq_new:N \g_ceur_ead_seq
\int_new:N \g_uad_int
\int_new:N \g_orcid_int
\seq_new:N \g_ceur_uad_seq
\seq_new:N \g_ceur_orcid_seq
\seq_new:N \g_ceur_contrib_role_seq

\newcommand\theead { \int_use:N \g_ead_int }

\NewDocumentCommand \@uad { O{} m }
   {
     \group_begin:
     \wrAux { \token_to_str:N \urlauthor
       { \exp_not:n {#2}}{\the\@eadauthor}}%
     \group_end:
   }

\NewDocumentCommand \urlauthor { m m } {
  \int_gincr:N \g_uad_int
  \seq_gput_right:Nn \g_ceur_uad_seq
  {
    { %\ttfamily \tl_to_str:n
      \url{ #1 } }
    \parsename { #2 }
    \space(\eadauthor)
  }
}
\NewDocumentCommand \@stmuads { }
  { \seq_use:Nn \g_ceur_uad_seq { ;~ } }

\NewDocumentCommand \@ead { m }
   {
     \group_begin:
     \wrAux { \token_to_str:N \emailauthor
       { \exp_not:n { #1 }}{ \the\@eadauthor }}
     \group_end:
   }

\newtoks \@eadauthor
\newbool{@cormark}

\NewDocumentCommand \emailauthor { m m }
{
  \int_gincr:N \g_ead_int
  \seq_gput_right:Nn \g_ceur_ead_seq
  {
    % { \ttfamily \tl_to_str:n { #1 } }
    { \href {mailto: #1 } { \protect\nolinkurl{#1} } }
    \parsename { #2 }
    \space(\eadauthor)%
  }
}

\NewDocumentCommand \@elseads { }
{
  \seq_use:Nn \g_ceur_ead_seq { ;~ }
}

\NewDocumentCommand \printemails { } {
  \group_begin:
  \int_compare:nNnTF { \int_use:N \g_ead_int } > { 0 } {
    \tex_let:D \thefootnote \relax \footnotetext {
      \raggedright
      \hspace*{-\parindent}
      % \hspace*{-\labelsep}
      \hspace*{-\footnotemargin}
      \bool_if:NTF \g_ceur_nologo_bool {
        \int_compare:nTF { \g_ead_int = 1 }
        { \textsc{email:\c_space_token} }
        { \textsc{email:\c_space_token} }
      }
      { \faIcon[regular]{envelope-open}\c_space_token }
      \seq_use:Nn \g_ceur_ead_seq { ;~ }
    }
  } {  }
  \group_end:
}

\NewDocumentCommand \printurls { } {
  \group_begin:
  \int_compare:nTF { \g_uad_int > 0 } {
    \tex_let:D \thefootnote \relax \footnotetext {
      \raggedright
      \hspace*{-\parindent}
      % \hspace*{-\labelsep}
      \hspace*{-\footnotemargin}
      \bool_if:NTF \g_ceur_nologo_bool
      { \textsc{url:\c_space_token} }
      { \faIcon{globe}\c_space_token }
      \seq_use:Nn \g_ceur_uad_seq { ;~ }
    }
  } { }
  \group_end:
}

%%
%% orcid
%%

\NewDocumentCommand \orcidauthor { m m } {
  \int_gincr:N \g_orcid_int
  \seq_gput_right:Nn \g_ceur_orcid_seq {
    % { \ttfamily \tl_to_str:n { #1 } }
    { \hrefurl { https://orcid.org/ #1 } { #1 } }
    \parsename{#2}
    \space(\eadauthor)
  }
}

\NewDocumentCommand \printorcid { } {
  \group_begin:
  \int_compare:nTF { \g_orcid_int > 0 } {
    \tex_let:D \thefootnote \relax \footnotetext {
      \raggedright
      \hspace*{-\parindent}
      % \hspace*{-\labelsep}
      \hspace*{-\footnotemargin}
      \bool_if:NTF \g_ceur_nologo_bool
      { \textsc{orcid:\c_space_token} }
      { \faIcon{orcid}\c_space_token }
      \seq_use:Nn \g_ceur_orcid_seq { ;~ }
    }
  } { }
  \group_end:
}

%
% Contrib Role
%

\seq_gclear_new:N \g_ceur_credits_seq

\NewDocumentCommand \ContribRole { m }
{
  \wrAux { \token_to_str:N \creditauthor
    { #1 } { \the\@eadauthor } }
}

\NewDocumentCommand \creditauthor { m m }
{
  \seq_gput_right:Nx \g_ceur_credits_seq
  { { \exp_not:N\bfseries #2 :}\space #1 }
}

\cs_set_eq:NN \credit \ContribRole

\NewDocumentCommand \printcredits { }
{
  \seq_if_empty:NF \g_ceur_credits_seq
  {
    \section*{CRediT ~authorship ~contribution ~statement}
    \seq_use:Nn \g_ceur_credits_seq { .~ }.
  }
}

\NewDocumentCommand \writemarks { m m }
   { \wrAux { \token_to_str:N \csgdef{mark@#1}{#2} } }

\seq_new:N \g_ceur_title_seq

\NewDocumentCommand \tnotemark { O{} }
   { \writemarks { title } { #1 } }

\NewDocumentCommand \@tnoteref { m }
   { \int_set:Nn \l_tmpa_int { 0 }
     \clist_map_inline:nn { #1 }
      {
%        \msg_term:n { ##1 .. [\cs:w X@##1:\cs_end:] }
        \cs_if_free:cTF { X@##1: }
          { \csdef{X@##1:}{0} }
          {
            \tl_set:Nx \l_tmpa_tl { \cs:w X@##1:\cs_end: }
            \int_case:nn { \l_tmpa_tl }
              {
                 { 1 }  { $^\star$ }
                 { 2 }  { $^{,\star\star}$ }
                 { 3 }  { $^{,\star\star\star}$ }
              }
          }
      }
    }

\seq_new:N \g_ceur_tnote_seq
\int_new:N \g_ceur_tnote_int

\NewDocumentCommand \tnotetext { O{} m }
   {
     \tl_if_head_eq_catcode:nNTF { #1 } a
       {
         % \msg_term:n { [TNOTE:~alpha] }%
         \seq_gput_right:Nn \g_ceur_tnote_seq
           { \int_incr:N \g_ceur_tnote_int
             \str_set:Nx \@currentlabel { \int_use:N \g_ceur_tnote_int }
              \ceurLabel { #1 }
             \renewcommand\thefootnote
              { \int_case:nn { \g_ceur_tnote_int }
                 {
                   { 1 } { $^\star$ }
                   { 2 }  { $^{\star\star}$ }
                   { 3 }  { $^{\star\star\star}$ }
                 }
              }
              \footnotetext { #2 }
            }
          }
        {
          % \msg_term:n { [TNOTE:~Number] }
          \seq_gput_right:Nn \g_ceur_tnote_seq
          {
            \int_set:Nn \l_tmpa_int { #1 }
            \renewcommand\thefootnote
              { \int_case:nn { \l_tmpa_int }
                {
                  { 1 } { $^\star$ }
                  { 2 }  { $^{\star\star}$ }
                  { 3 }  { $^{\star\star\star}$ }
                }
              }
             \footnotetext { #2 }
           }
         }
       }

\newcommand \printtnotes { \seq_use:Nn \g_ceur_tnote_seq { \par } }

\seq_new:N \g_ceur_nonumnote_seq

\NewDocumentCommand \nonumnote { m }
{
  \group_begin:
  \seq_gput_right:Nn \g_ceur_nonumnote_seq
  {
    \tex_def:D \thefootnote { }
    \footnotetext{%
      % \raggedright
      % \hspace*{-\parindent}
      % % \hspace*{-\labelsep}
      % \hspace*{-\footnotemargin}
      #1}
  }
  \group_end:
}

\newcommand \printnonumnotes { \seq_use:Nn \g_ceur_nonumnote_seq { \par } }

\seq_new:N \g_ceur_fnote_seq
\int_new:N \g_ceur_fnote_int

\NewDocumentCommand \fntext { O{} m } {
  \tl_if_head_eq_catcode:nNTF { #1 } a {
    % \msg_term:n { [FN:~alpha] }%
    \seq_gput_right:Nn \g_ceur_fnote_seq {
      \int_incr:N \g_ceur_fnote_int
      \str_set:Nx \@currentlabel { \int_use:N \g_ceur_fnote_int }
      \ceurLabel { #1 }
      % \tex_def:D \thefootnote { \int_use:N \g_ceur_fnote_int }
      \tex_def:D \thefootnote {
        \int_case:nn { \g_ceur_tnote_int } {
          { 1 } { $^{\dagger}$ }
          { 2 } { $^{\ddagger}$ }
          { 3 } { $^{\S}$ }
          { 4 } { $^{\P}$ }
          { 5 } { $^{\|}$ }
        }
      }
      \footnotetext { #2 }
    }
  } {
    % \msg_term:n { [FN:~Number] }
    \seq_gput_right:Nn \g_ceur_fnote_seq {
      \int_set:Nn \l_tmpa_int { #1 }
      % \tex_def:D \thefootnote { \int_use:N \l_tmpa_int }
      \tex_def:D \thefootnote {
        \int_case:nn { \l_tmpa_int } {
          { 1 } { $^{\dagger}$ }
          { 2 } { $^{\ddagger}$ }
          { 3 } { $^{\S}$ }
          { 4 } { $^{\P}$ }
          { 5 } { $^{\|}$ }
        }
      }
      \footnotetext { #2 }
    }
  }
}

\newcommand \printfnotes { \seq_use:Nn \g_ceur_fnote_seq { \par } }

\seq_new:N \g_ceur_cor_seq
\int_new:N \g_ceur_cor_int

\NewDocumentCommand \cortext { O{} m } {
  \tl_if_head_eq_catcode:nNTF { #1 } a  {
    % \msg_term:n { [COR:~alpha] }%
    \seq_gput_right:Nn \g_ceur_cor_seq {
      \int_incr:N \g_ceur_cor_int
      \str_set:Nx \@currentlabel { \int_use:N \g_ceur_cor_int }
      \ceurLabel { #1 }
      \tex_def:D \thefootnote {
        \int_case:nn { \g_ceur_cor_int } {
          { 1 } { $\ast$ }
          { 2 } { $\ast\!\ast$ }
          { 3 } { $\ast\!\ast\!\ast$ }
        }
      }
      \footnotetext { \noindentfoot #2 }
    }
  } {
    % \msg_term:n { [COR:~Number] }
    \seq_gput_right:Nn \g_ceur_cor_seq {
      \int_set:Nn \l_tmpa_int { #1 }
      \tex_def:D \thefootnote {
        \int_case:nn { \l_tmpa_int } {
          { 1 } { $\ast$ }
          { 2 } { $\ast\!\ast$ }
          { 3 } { $\ast\!\ast\!\ast$ }
        }
      }
      \footnotetext { #2 }
    }
  }
}

\newcommand \printcornotes { \seq_use:Nn \g_ceur_cor_seq { \par } }

\NewDocumentCommand \process@marks { } {
  \cs_if_free:cTF { mark@corau\theauthor }
  { \ignorespaces }
  { \str_set:Nx \l_tmpa_str { \use:c{ mark@corau\theauthor } }
    \int_case:nn { \l_tmpa_str } {
      { 1 } { \sep$\ast$ }
      { 2 } { \sep$\ast\ast$ }
      { 3 } { \sep$\ast\!\ast\!\ast$ }
    }
    \tex_def:D \sep{\unskip,}
  }
  %%
  \cs_if_free:cTF { mark@fnau\theauthor }
  { \ignorespaces }
  { \str_set:Nx \l_tmpa_str { \use:c{ mark@fnau\theauthor } }
    \int_case:nn { \l_tmpa_str } {
      { 1 } { \sep${\dagger}$ }
      { 2 } { \sep${\ddagger}$ }
      { 3 } { \sep${\S}$ }
      { 4 } { \sep${\P}$ }
      { 5 } { \sep${\|}$ }
    }
    \tex_def:D \sep{\unskip,}
  }
}

%%
%% Author macros
%%

\seq_new:c { g_ceur_au0_seq }
\seq_new:c { g_ceur_clau0_seq }
\int_new:N \g_ceur_au_int
\int_new:N \g_ceur_aau_int

\NewDocumentCommand \ResetMarks { } {
  \keys_set:nn { ceur / author } {
    auid       = {} ,
    bioid      = {} ,
    alt        = {} ,
    style      = { normal } ,
    prefix     = {} ,
    suffix     = {} ,
    degree     = {} ,
    role       = {} ,
    orcid      = {} ,
    collab     = { false }  ,
    type       = { author } ,
    anon       = { false }  ,
    deceased   = { false }  ,
    twitter    = {} ,
    facebook   = {} ,
    linkedin   = {} ,
    plus       = {} ,
    gplus      = {} ,
    email      = {} ,
    url        = {} ,
  }
  \tex_gdef:D \sep{}
  \tex_gdef:D \ceur@corref{}
  \tex_gdef:D \@fnmark {}
}

\int_new:N \l_autype_int
\keys_define:nn { ceur / author } {
  auid     .tl_set:N   = \l_ceur_au_id_tl             ,
  bioid    .tl_set:N   = \l_ceur_au_bioid_tl          ,
  alt      .tl_set:N   = \l_ceur_au_alt_tl            ,
  style    .tl_set:N   = \l_ceur_au_style_tl          ,
  prefix   .tl_set:N   = \l_ceur_au_prefix_tl         ,
  suffix   .tl_set:N   = \l_ceur_au_suffix_tl         ,
  degree   .tl_set:N   = \l_ceur_au_degree_tl         ,
  role     .tl_set:N   = \l_ceur_au_role_tl           ,
  orcid    .tl_set:N   = \l_ceur_au_orcid_tl          ,
  collab   .bool_set:N = \l_ceur_au_collab_bool       ,
  type     .multichoice:                              ,
  type/author    .code:n = { \int_set:Nn \l_autype_int { 0 } },
  type/editor    .code:n = { \int_set:Nn \l_autype_int { 1 } },
  type/collab    .code:n = { \int_set:Nn \l_autype_int { 2 } },
  type/anon      .code:n = { \int_set:Nn \l_autype_int { 3 } },
  % type/collab    .bool_set:N = \l_ceur_au_collab_bool          ,
  % type/anon      .bool_set:N = \l_ceur_au_anon_bool            ,
  anon      .bool_set:N = \l_ceur_au_anon_bool        ,
  deceased  .bool_set:N = \l_ceur_au_deceased_bool    ,
  twitter   .tl_set:N   = \l_ceur_au_twitter_tl       ,
  facebook  .tl_set:N   = \l_ceur_au_facebook_tl      ,
  linkedin  .tl_set:N   = \l_ceur_au_linkedin_tl      ,
  plus      .tl_set:N   = \l_ceur_au_gplus_tl         ,
  gplus     .tl_set:N   = \l_ceur_au_gplus_tl         ,
  email     .tl_set:N   = \l_ceur_au_email_tl         ,
  %% prevent URL expansion (due ~ sign)
  url       .code:n   = { \tl_set:Nn \l_ceur_au_url_tl { \exp_not:n { #1 } } },
}

\keys_set:nn { ceur / author } {
  auid       = {} ,
  bioid      = {} ,
  alt        = {} ,
  style      = { normal } ,
  prefix     = {} ,
  suffix     = {} ,
  degree     = {} ,
  role       = {} ,
  orcid      = {} ,
  collab     = { false }  ,
  type       = { author } ,
  anon       = { false }  ,
  deceased   = { false }  ,
  twitter    = {} ,
  facebook   = {} ,
  linkedin   = {} ,
  plus       = {} ,
  gplus      = {} ,
  email      = {} ,
  url        = {} ,
}

\keys_define:nn { ceur / ausetup } {
  type      .choice: ,
  type / authors .meta:n = {
    size   =  \large         ,
    shape  =  \upshape       ,
    weight =  \mdseries      ,
    before =  \bigskipamount ,
    after  =  0pt            ,
    align  =  \raggedright   ,
    color  =  black          ,
    lskip  =  0pt            ,
    rskip  =  0pt            ,
  } ,
  type / collaboration .meta:n = {
    size   =  \Large         ,
    shape  =  \upshape       ,
    weight =  \mdseries      ,
    before =  \bigskipamount ,
    after  =  0pt            ,
    align  =  \raggedright   ,
    color  =  black          ,
    lskip  =  0pt            ,
    rskip  =  0pt            ,
  } ,
  size      .tl_set:N    = \l_ceur_augroup_size_tl      ,
  shape     .tl_set:N    = \l_ceur_augroup_shape_tl     ,
  weight    .tl_set:N    = \l_ceur_augroup_weight_tl    ,
  before    .dim_set:N   = \l_ceur_augroup_before_dim   ,
  after     .dim_set:N   = \l_ceur_augroup_after_dim    ,
  align     .tl_set:N    = \l_ceur_augroup_align_tl     ,
  color     .tl_set:N    = \l_ceur_augroup_color_tl     ,
  lskip     .dim_set:N   = \l_ceur_augroup_lskip_tl     ,
  rskip     .dim_set:N   = \l_ceur_augroup_rskip_tl     ,
}

\DeclareDocumentCommand \ceurAuthorSetup { m } {
  \keys_set:nn { ceur / ausetup } { #1 }
}
\DeclareDocumentCommand \ceurausetup { m } {
  \tl_set:Nn \l_ceur_au_setup_tl {
    \keys_set:nn { ceur / ausetup } { #1 } }
}
\DeclareDocumentCommand \ceurclbsetup { m } {
  \tl_set:Nn \l_ceur_clb_setup_tl {
    \keys_set:nn { ceur / ausetup } { #1 } }
}

\ceurausetup { }
\ceurclbsetup { }

\seq_new:N  \g_ceur_maltese_seq
\seq_new:N  \g_ceur_facebook_seq
\seq_new:N  \g_ceur_twitter_seq
\seq_new:N  \g_ceur_gplus_seq
\seq_new:N  \g_ceur_linkedin_seq

\NewDocumentCommand \twitterauthor { m m } {
  \seq_gput_right:Nn \g_ceur_twitter_seq {
    \parsename { #2 }
    \url{https://twitter.com/\tl_to_str:n{#1}}\space(\eadauthor)
  }
}
\NewDocumentCommand \facebookauthor { m m }
   {
     \seq_gput_right:Nn \g_ceur_facebook_seq
       {
         \parsename { #2 }
         \url{https://www.facebook.com/\tl_to_str:n{#1}}\space(\eadauthor) %
       }
     }
\NewDocumentCommand \gplusauthor { m m }
   {
     \seq_gput_right:Nn \g_ceur_gplus_seq
       {
         \parsename { #2 }
         \url{https://plus.google.com/\tl_to_str:n{#1}}\space(\eadauthor)%
       }
     }
\NewDocumentCommand \linkedinauthor { m m }
   {
     \seq_gput_right:Nn \g_ceur_linkedin_seq
       {
         \parsename { #2 }
         % \url{https://www.linkedin.com/profile/view?id=\tl_to_str:n{#1}}%
         \url{https://www.linkedin.com/in/\tl_to_str:n{#1}}%
         \space(\eadauthor)
       }
     }

\NewDocumentCommand \printmaltese { }
    {
      \seq_use:Nn { \g_ceur_maltese_seq } { }
    }
\NewDocumentCommand \printfacebook { }
    {
      \seq_if_empty:NTF \g_ceur_facebook_seq { }
        {
          \tex_def:D \thefootnote{}
          \footnotetext
          {
            \bool_if:NTF \g_ceur_nologo_bool
             { Facebook:\c_space_token }
             { \faIcon{facebook-f}\c_space_token }
            \seq_use:Nn \g_ceur_facebook_seq {,\c_space_token }
          }
        }
      }
\NewDocumentCommand \printtwitter { }
    {
      \seq_if_empty:NTF \g_ceur_twitter_seq { }
        {
          \tex_def:D \thefootnote{}
          \footnotetext
          {
            \bool_if:NTF \g_ceur_nologo_bool
             { Twitter:\c_space_token }
             { \faIcon{twitter}\c_space_token }
            \seq_use:Nn \g_ceur_twitter_seq {,\c_space_token }
          }
        }
      }
\NewDocumentCommand \printgplus { }
    {
      \seq_if_empty:NTF \g_ceur_gplus_seq { }
        {
          \tex_def:D \thefootnote{}
          \footnotetext
          {
            \bool_if:NTF \g_ceur_nologo_bool
             { Google+:\c_space_token }
             { \faIcon{google-plus-g}\c_space_token }
            \seq_use:Nn \g_ceur_gplus_seq {,\c_space_token }
          }
        }
      }
\NewDocumentCommand \printlinkedin { }
    {
      \seq_if_empty:NTF \g_ceur_linkedin_seq { }
        {
          \tex_def:D \thefootnote{}
          \footnotetext
          {
            \bool_if:NTF \g_ceur_nologo_bool
             { LinkedIn:\c_space_token }
             { \faIcon{linkedin-in}\c_space_token }
            \seq_use:Nn \g_ceur_linkedin_seq {,\c_space_token }
          }
        }
      }

\seq_new:N \g_ceur_prelimsau_seq

\csxdef { infoauthors } { }
\csgdef { pdfxauthors } { }

\csgdef { __short_authors_tmp } { }
% Number of person in short authors list
\int_new:N \g_num_short_authors
\g_num_short_authors = 1

\cs_new:Nn \no_break_space: { \nobreak{~} \penalty 10000 }

\RenewDocumentCommand \author { O{} m O{} } {
  \ResetMarks
  \tl_if_blank:nTF { #3 } { }
  { \keys_set:nn { ceur / author } { #3 } }
  %
  \int_gincr:N \g_ceur_au_int
  \tex_gdef:D \theau@ { \int_use:N \g_ceur_au_int }
  %
  \seq_gput_right:Nn \g_ceur_prelimsau_seq { #2 }
  \bool_if:NTF \l_ceur_au_collab_bool
  { \seq_gput_right:cn { g_ceur_clau\int_use:N \g_ceur_augr_int _seq } }
  { \seq_gput_right:cn { g_ceur_au\int_use:N \g_ceur_augr_int _seq } }
  {
    \int_gincr:N \g_ceur_aau_int
    \tex_gdef:D \theauthor {\int_use:N \g_ceur_aau_int }
    \keys_set:nn { ceur / author } { #3 }
    \tl_if_head_eq_catcode:nNTF { #1 } a
    { \processAffRef { #1 } }
    { \processAffNum { #1 } }
    \tl_if_empty:NF \l_ceur_au_prefix
    { \l_ceur_au_prefix_tl \c_space_token }
    \str_if_eq:VnTF \l_ceur_au_style_tl  { chinese } {
      % \msg_term:n {STYLE~T=\l_ceur_au_style_tl........}
      \invparsename { #2 }
      \textcolor{\l_ceur_augroup_color_tl}{\surname}
      \no_break_space:
      \textcolor{\l_ceur_augroup_color_tl !50}{\firstname}
    }{
      % \msg_term:n {STYLE~F=\l_ceur_au_style_tl........}
      \parsename { #2 }
      \textcolor{\l_ceur_augroup_color_tl !50}{\firstname}
      \no_break_space:
      \textcolor{\l_ceur_augroup_color_tl}{\surname}
    }
    \tl_if_empty:NF \l_ceur_au_suffix_tl
    { \c_space_token \l_ceur_au_suffix_tl }
    \unskip
    \textsuperscript
    {
      \tl_if_blank:nTF { #1 }
      { \tex_def:D \sep{} }
      { {\itshape\listAff} \tex_def:D \sep{\unskip,} }
      \process@marks
      \bool_if:NT \l_ceur_au_deceased_bool
      { \sep \maltese
        \tex_def:D \sep { \unksip, }
      }
    }
    \tl_if_empty:NF \l_ceur_au_degree_tl
    { ,\c_space_token \l_ceur_au_degree_tl }
    \tl_if_empty:NF \l_ceur_au_role_tl
    { \c_space_token (\l_ceur_au_role_tl) }
    %
    \ResetMarks
  }
  %
  \bool_if:NT \l_ceur_au_deceased_bool
  {
    \seq_gput_right:Nn \g_ceur_maltese_seq
    {
      \tex_def:D \thefootnote { \maltese }
      \footnotetext{Deceased~author.}
    }
  }
  \tl_if_empty:NF \l_ceur_au_email_tl {
    \wrAux { \token_to_str:N \emailauthor
      { \l_ceur_au_email_tl } { \exp_not:n {#2} } }
  }
  \tl_set:Nx \l_ceur_au_url_tl_tmp { \l_ceur_au_url_tl }
  \tl_if_empty:NF \l_ceur_au_url_tl_tmp {
    \wrAux { \token_to_str:N \urlauthor
      { \l_ceur_au_url_tl } { \exp_not:n {#2} } }
  }
  % various social media
  \tl_if_empty:NTF \l_ceur_au_facebook_tl { }
  {
    \wrAux { \token_to_str:N \facebookauthor
      { \l_ceur_au_facebook_tl } { \exp_not:n {#2} } }
  }
  \tl_if_empty:NF \l_ceur_au_twitter_tl
  {
    \wrAux { \token_to_str:N \twitterauthor
      { \l_ceur_au_twitter_tl } { \exp_not:n {#2} } }
  }
  \tl_if_empty:NF \l_ceur_au_gplus_tl
  {
    \wrAux { \token_to_str:N \gplusauthor
      { \l_ceur_au_gplus_tl } { \exp_not:n {#2} } }
  }
  \tl_if_empty:NF \l_ceur_au_linkedin_tl
  {
    \wrAux { \token_to_str:N \linkedinauthor
      { \l_ceur_au_linkedin_tl } { \exp_not:n {#2} } }
  }
  \tl_if_empty:NF \l_ceur_au_orcid_tl
  {
    \wrAux { \token_to_str:N \orcidauthor
      { \l_ceur_au_orcid_tl } { \exp_not:n {#2} } }
  }
  % Short authors list
  \csgdef { __short_authors_tmp } { #2 }
  \int_compare:nNnTF { \theau@ } = { 1 } {
    \xappto \__short_authors: { \__short_authors_tmp }
  }{
    \int_compare:nNnTF { \theau@ } < { \g_num_short_authors + 1 } {
      \xappto \__short_authors: { , ~ \__short_authors_tmp }
    }{
      \int_compare:nNnTF { \theau@ } = { \g_num_short_authors + 1 } {
        \xappto \__short_authors: { ~et~al. }
      }{ }
    }
  }
  %
  \@eadauthor={#2}
  \pdfstringdef\__info_au: { #2 }
  \int_compare:nNnTF { \theau@ } < { 4 }
  { \xappto \infoauthors { \__info_au: , ~ } }
  {
    \int_compare:nNnTF { \theau@ } = { 4 }
    { \xappto \infoauthors { et~al. } }
    { }
  }
  % Authors list for PDF/A
  \csgdef { __pdfxauthor } { #2 }
  \int_compare:nNnTF { \theau@ } = { 1 }
  { \xappto \pdfxauthors { \detokenize\expandafter{\__pdfxauthor} } }
  { \xappto \pdfxauthors { \iow_char:N \\ sep ~ \detokenize\expandafter{\__pdfxauthor} } }
}

\NewDocumentCommand \ceurauthors { } {
  \group_begin:
  \ceurAuthorSetup { type = authors }
  \l_ceur_au_setup_tl
  \par \vskip\l_ceur_augroup_before_dim
  \l_ceur_augroup_align_tl
  \l_ceur_augroup_size_tl
  \l_ceur_augroup_shape_tl
  \l_ceur_augroup_weight_tl
  \color{ \l_ceur_augroup_color_tl }
  \bool_if:NTF \g_ceur_augr_bool
  { \seq_use:Nn \g_ceur_augr_seq { \par } }
  {
    \seq_use:cnnn { g_ceur_au\int_use:N\g_ceur_augr_int _seq }
    { ,~ } { ,~ } { ~and~ }
  }
  \par\vskip\l_ceur_augroup_after_dim
  \group_end:
}

\seq_new:c { g_ceur_collab0_seq }
\bool_new:N \g_ceur_in_clau_bool

\NewDocumentCommand \ceurcollab { } {
  \bool_if:NTF \g_ceur_augr_bool
  { }
  {
    \group_begin:
    \ceurAuthorSetup { type = collaboration }
    \l_ceur_clb_setup_tl
    \par \vskip \l_ceur_augroup_before_dim
    \l_ceur_augroup_align_tl
    \l_ceur_augroup_size_tl
    \l_ceur_augroup_shape_tl
    \l_ceur_augroup_weight_tl
    \color{ \l_ceur_augroup_color_tl }
    \seq_use:cn {g_ceur_collab\int_use:N \g_ceur_aaugr_int _seq} { }
    \seq_use:cnnn {g_ceur_clau\int_use:N \g_ceur_aaugr_int _seq}
    { ~and~ } { ,~ } { ~and~ }
    \par \vskip \l_ceur_augroup_after_dim
    \group_end:
  }
}

\newenvironment{collaboration}[1][] {
  \seq_gput_right:cn {g_ceur_collab\int_use:N \g_ceur_augr_int _seq}
  { \textit{Collaboration:~} #1 \par \smallskip }
}{
}

\NewDocumentCommand \dept  { m } { #1 }
\NewDocumentCommand \divn  { m } { #1 }
\NewDocumentCommand \aline { m } { #1 }
\NewDocumentCommand \city  { m } { #1 }
\NewDocumentCommand \cnty  { m } { #1 }
\NewDocumentCommand \phone { m } { #1 }
\NewDocumentCommand \fax   { m } { #1 }
\NewDocumentCommand \aurl  { m } { #1 }

\seq_new:c { g_ceur_aff0_seq }
\int_new:N \g_ceur_aff_int
\tl_new:N \l_addrtype_tl

\keys_define:nn { ceur / address }
   {
     foot     .bool_gset:N  = \g_ceur_addr_foot_bool       ,
     name     .tl_set:N    = \l_ceur_addr_name_tl          ,
     type     .multichoice:                               ,
      type/alt     .code:n = { \tl_set:Nn \l_ceur_addr_type_tl
          { Alternate~address } }  ,
      type/addl    .code:n = { \tl_set:Nn \l_ceur_addr_type_tl
          { Additional~address } } ,
      type/regular .code:n = { \tl_set:Nn \l_ceur_addr_type_tl
          {  } } ,
      type/custom  .code:n = { \tl_set:Nn \l_ceur_addr_type_tl
          { \l_ceur_addr_name_tl } } ,
   }
\DeclareDocumentCommand \ceurAddrSetup { m  }
   { \keys_set:nn { ceur / address } { #1 } }

\keys_set:nn { ceur / address }
{
  foot       = { false }   ,
  type       = { regular } ,
  name       = { Alternate~address } ,
}

\cs_new:Nn \__reset_addr:
{
  \bool_gset_false:N \g_ceur_addr_foot_bool
  \tl_set:Nn \l_ceur_addr_type_tl {  }
  \tl_set:Nn \l_ceur_addr_name_tl { Alternate~address }
}

\seq_new:N \g_ceur_aff_foot_seq

\NewDocumentCommand \printaddrinfoot { }
{
  { \seq_use:Nn \g_ceur_aff_foot_seq { \par } }
}

\NewDocumentCommand \address { O{} m O{} }
{
  \__reset_addr:
  \keys_set:nn { ceur / address } { #3 }
  \bool_if:NTF \g_ceur_addr_foot_bool
  { \__foot_address:nnn [#1]{#2}[#3] }
  {
    \seq_gput_right:cn { g_ceur_aff\int_use:N \g_ceur_augr_int _seq }
    { \tl_if_blank:nTF { #1 }
      {
        \tex_xdef:D \thefootnote{}
        { #2 }
      }
      {
        \tl_if_head_eq_catcode:nNTF { #1 } a
        {
          \int_gincr:N \g_ceur_aff_int
          \tex_xdef:D \@currentlabel
          %% label format:
          %% \int_to_arabic:n
          %% \int_to_alph:n
          %% \int_to_symbols:nnn
          %% \int_to_roman:n
          { \int_to_arabic:n { \int_use:N \g_ceur_aff_int } }
          \ceurLabel {#1}
          \textsuperscript{\itshape\@currentlabel} #2
        }
        {
          \int_gset:Nn \g_ceur_aff_int { #1 }
          \tex_xdef:D \@currentlabel
          { \int_to_arabic:n {  \int_use:N \g_ceur_aff_int } }
          \textsuperscript{\itshape\@currentlabel} #2
        }
      }
    }
  }
}

\cs_new:Npn \__foot_address:nnn [#1]#2[#3]
{
  \keys_set:nn { ceur / address } { #3 }
  \seq_gput_right:cn { g_ceur_aff_foot_seq }
  {
    \tl_if_empty:nTF { #1 }
    {
      \tl_if_empty:NTF \l_ceur_addr_type_tl
      { \footnotetext{#2} }
      {
        \footnotetext{\textit{\l_ceur_addr_type_tl}:
          \c_space_token #2 }
      }
    }
    {
      \tl_if_head_eq_catcode:nNTF { #1 } a
      %
      {
        \tex_def:D \thefootnote{\itshape\@currentlabel}
        \tl_if_empty:NTF \l_ceur_addr_type_tl
        { \footnotetext{#2} }
        { \footnotetext{\textit{\l_ceur_addr_type_tl}: \c_space_token #2} }
      }
      {
        \tex_def:D \thefootnote { \itshape\int_to_arabic:n { #1 } }
        \tl_if_empty:NTF \l_ceur_addr_type_tl
        { \footnotetext{#2} }
        { \footnotetext{\textit{\l_ceur_addr_type_tl}:
            \c_space_token #2 } }
      }
    }
  }
}

\keys_define:nn { ceur / affsetup }
   {
     type      .choice: ,
     type / normal .code:n =
       { \tl_set:Nn \l_ceur_aff_type_tl { 0 } } ,
     type / nonum .code:n =
       { \tl_set:Nn \l_ceur_aff_type_tl { 1 } } ,

     size      .tl_set:N    = \l_ceur_aff_size_tl      ,
     shape     .tl_set:N    = \l_ceur_aff_shape_tl     ,
     weight    .tl_set:N    = \l_ceur_aff_weight_tl    ,
     before    .dim_set:N   = \l_ceur_aff_before_dim   ,
     after     .dim_set:N   = \l_ceur_aff_after_dim    ,
     align     .tl_set:N    = \l_ceur_aff_align_tl     ,
     color     .tl_set:N    = \l_ceur_aff_color_tl     ,
     lskip     .dim_set:N   = \l_ceur_aff_lskip_dim    ,
     rskip     .dim_set:N   = \l_ceur_aff_rskip_dim    ,
   }

\DeclareDocumentCommand \ceurAffSetup { m }
   { \keys_set:nn { ceur / affsetup } { #1 } }
\DeclareDocumentCommand \ceuraffsetup { m }
   { \tl_set:Nn \l_ceur_aff_setup_tl
     { \keys_set:nn { ceur / affsetup } { #1 } }
   }
\ceuraffsetup {
    size   = \footnotesize,
    shape  = \itshape,
    color  = black,
    before = 0pt,
    weight = \mdseries,
    align  = \raggedright,
    }

\NewDocumentCommand \ceuraddress { }
   {
     \bool_if:NTF \g_ceur_augr_bool
     { }
     {
       \group_begin:
       \ceurAffSetup { type = normal }
       \l_ceur_aff_setup_tl
       \par \vskip\l_ceur_aff_before_dim
       \l_ceur_aff_align_tl
       \l_ceur_aff_size_tl
       \l_ceur_aff_shape_tl
       \l_ceur_aff_weight_tl
       \color{ \l_ceur_aff_color_tl }
       \seq_use:cn { g_ceur_aff\int_use:N \g_ceur_aaugr_int _seq }
       { \par\vskip2pt  }
       \par\vskip\l_ceur_aff_after_dim
       \group_end:
     }
   }

\int_new:N \g_ceur_augr_int
\seq_new:N \g_ceur_augr_seq
\int_new:N \g_ceur_aaugr_int
\bool_new:N \g_ceur_augr_bool

\NewDocumentEnvironment { augroup } { }
{
  \bool_gset_true:N \g_ceur_augr_bool
  \int_gincr:N \g_ceur_augr_int
  \seq_new:c {g_ceur_au\int_use:N \g_ceur_augr_int _seq}
  \seq_new:c {g_ceur_aff\int_use:N \g_ceur_augr_int _seq}
  \seq_new:c {g_ceur_collab\int_use:N \g_ceur_augr_int _seq}
  \seq_new:c {g_ceur_clau\int_use:N \g_ceur_augr_int _seq}
  \msg_term:n { AUGR:~\int_use:N \g_ceur_augr_int ... }
}
{
  \seq_gput_right:Nn \g_ceur_augr_seq
  {
    \int_gincr:N \g_ceur_aaugr_int
    \group_begin:
    \ceurAuthorSetup { type = collaboration }
    \l_ceur_clb_setup_tl
    \par \vskip \l_ceur_augroup_before_dim
    \l_ceur_augroup_align_tl
    \l_ceur_augroup_size_tl
    \l_ceur_augroup_shape_tl
    \l_ceur_augroup_weight_tl
    \color{ \l_ceur_augroup_color_tl }
    \seq_use:cnnn { g_ceur_au\int_use:N \g_ceur_aaugr_int _seq }
    { ~and~ } { ,~ } { ~and~ }
    \par \vskip \l_ceur_augroup_after_dim
    \group_end:
    %
    \group_begin:
    \ceurAffSetup { type = normal }
    \l_ceur_aff_setup_tl
    \par \vskip\l_ceur_aff_before_dim
    \l_ceur_aff_align_tl
    \l_ceur_aff_size_tl
    \l_ceur_aff_shape_tl
    \l_ceur_aff_weight_tl
    \color{ \l_ceur_aff_color_tl }
    \seq_use:cn { g_ceur_aff\int_use:N \g_ceur_aaugr_int _seq }
    { \par \smallskip }
    \par\vskip\l_ceur_aff_after_dim
    \msg_term:n { AAUGR:~\int_use:N \g_ceur_aaugr_int ... }
    \group_end:
    %
    \group_begin:
    \ceurAuthorSetup { type = collaboration }
    \l_ceur_clb_setup_tl
    \par \vskip \l_ceur_augroup_before_dim
    \l_ceur_augroup_align_tl
    \l_ceur_augroup_size_tl
    \l_ceur_augroup_shape_tl
    \l_ceur_augroup_weight_tl
    \color{ \l_ceur_augroup_color_tl }
    \seq_use:cn {g_ceur_collab\int_use:N \g_ceur_aaugr_int _seq} { }
    \seq_use:cnnn {g_ceur_clau\int_use:N \g_ceur_aaugr_int _seq}
    { ~and~ } { ,~ } { ~and~ }
    \par\vskip \l_ceur_augroup_after_dim
    \group_end:
  }
}

%%
%% Abstract
%%

\RequirePackage{moreverb}

\tl_new:N \l_ceur_abs_title_tl
\box_new:N \g_ceur_abs_box

\tex_gdef:D \abstractname { \textbf{\sffamily Abstract} }

\NewDocumentEnvironment { Abstract } { o } {
  % \global\setbox \g_ceur_abs_box = \vtop \bgroup
  % \hsize = .65 \textwidth \parindent \z@
  \group_begin:
  % Check if abstract exist
  \file_if_exist:nT { \jobname.abs } {
    \IfNoValueTF { #1 } {
    } { \tex_gdef:D \abstractname { #1 } }
    \parindent \z@
    \leftskip = .1 \textwidth
    % \box_if_empty:NTF \g_ceur_key_box
    % { \leftskip = .1 \textwidth }
    % {
    % \dim_gset:Nn \l_tmpa_dim { \box_ht:N \g_ceur_key_box }
    % \dim_gadd:Nn \l_tmpa_dim { \box_dp:N \g_ceur_key_box }
    % \leftskip .1\textwidth
    % \hspace*{-.1 \textwidth }
    % \noindent\hbox_to_wd:nn {  \z@ } { \box \g_ceur_key_box }
    % \skip_vertical:n { - \l_tmpa_dim }
    % }
    \skip_vertical:n { \baselineskip }
    % \noindent \abstractname \par
    \noindent { \textbf{\sffamily Abstract} } \par
    % \skip_vertical:n { -4pt}
    % \noindent \rule{.65\textwidth}{.2pt}\par
    \footnotesize
    \ignorespaces \everypar { \parindent=1.5em }
  } { }
} {
  \par
  \noindent\hbox_to_wd:nn { \z@ } { \box \g_ceur_key_box }
  \par \group_end:
}

\NewDocumentEnvironment { PrelimsAbstract } { O{} } {
  \parindent=0pt
  { \fontsize{14pt}{16pt}\selectfont #1 }\par
  \vskip12pt
  { \fontsize{12pt}{14pt}\bfseries\selectfont\casprelimstitle } \par
  \vskip6pt
  \seq_use:Nn \g_ceur_prelimsau_seq { , }
  \vskip12pt
  \par
} { }

\RenewDocumentEnvironment { abstract } { o } {
  \IfNoValueTF { #1 } {
  } { \tex_gdef:D \abstracttitle { #1 } }
  \verbatimwrite{\jobname.abs}
} { \endverbatimwrite }

\newbox\casgrabsbox
\newbox\casauhlbox
\newbool { usecasgrabsbox }
\newbool { usecashlsbox }

\DeclareDocumentEnvironment { graphicalabstract } { O{Graphical~Abstract} } {
  \global \booltrue { usecasgrabsbox }
  \global\setbox\casgrabsbox=\vbox\bgroup
  \begin{PrelimsAbstract}[#1]
  \noindent \ignorespaces
} {
  \end{PrelimsAbstract}
  \egroup
}

\DeclareDocumentEnvironment { highlights } { O{Highlights} } {
  \global \booltrue { usecashlsbox }
  \global\setbox\casauhlbox=\vbox\bgroup
  \begin{PrelimsAbstract}[#1]
  \noindent \ignorespaces
  \begin{itemize}
} {
  \end{itemize}
  \end{PrelimsAbstract}
  \egroup
}

\NewDocumentCommand \dashrule { O{.4pt} m m }
   {
     % \color{black!50}
     \skip_vertical:n { #2 }
     % \noindent \rule { \linewidth } { #1}
     \normalcolor \skip_vertical:n { #3 }
   }

\NewDocumentCommand \keywordtitle { } { Keywords }
\NewDocumentCommand \keywordtitlesep { } {:\c_space_token }
\box_new:N \g_ceur_key_box

\NewDocumentCommand \MSC { O{} m }
   {
     \par\noindent \textit { #1\c_space_token MSC:\c_space_token } #2
   }
\NewDocumentCommand \JEL { m }
   {
     \par\noindent \textit { JEL:\c_space_token } #1
   }
\NewDocumentCommand \PACS { m }
   {
     \par\noindent \textit { PACS:\c_space_token } #1
   }

\NewDocumentEnvironment { keywords } { +b } {
  %% Keywords list for PDF/A
  \csgdef { pdfxkeywords } { \detokenize\expandafter{ #1 } }
  %% replace \sep by commas
  \tex_global:D \tex_setbox:D \g_ceur_key_box = \vtop \bgroup
  \hsize=.9 \textwidth
  \vspace*{0pt}
  \cs_new:Nn \sep: {\unskip,~}
  \cs_set_eq:NN \sep \sep:
  %% Environment block
  \parindent \z@
  \noindent \textbf {\sffamily \keywordtitle }  \par
  \footnotesize
  #1
  \skip_vertical:n { \baselineskip }
  \egroup
} { }

%% Acknowledgments

\NewDocumentEnvironment { acknowledgments } { }
{
  \group_begin:
  \section*{Acknowledgments}
}
{ \group_end: }


%% Copyright

\def\copyrightyear#1{\def\@copyrightyear{#1}}
\copyrightyear{\the\year}

\DeclareRobustCommand\copyrightclause[1]{%
  \def\@copyrightclause{#1}%
}
\let\@copyrightclause\@empty
% \copyrightclause{\textcolor{red}{Author: Please provide a copyright holder}}

%% CC-BY logo
\RequirePackage{csquotes}
\RequirePackage[type={CC},modifier={by},version={4.0},imageposition=left]{doclicense}

%% CC-BY logo width
\newdimen\ccLogoWidth
\ccLogoWidth=3.5em

\def\@copyrightLine{%
  % \setbox\@tempboxa\hbox{\includegraphics[height=\baselineskip,clip]{cc-by}}%
  % \ccLogoWidth=\dimexpr\wd\@tempboxa
  % \@rightskip\@flushglue \rightskip\@rightskip
  % % \hangindent\dimexpr\wd\@tempboxa+0.5em\relax
  % \begin{minipage}[c]{\ccLogoWidth}
  %   \href{https://creativecommons.org/licenses/by/4.0}%
  %   {\lower\baselineskip\hbox{\unhcopy\@tempboxa}}\enskip
  % \end{minipage}
  % \nobreak\enskip
  % \begin{minipage}[c]{\linewidth - \ccLogoWidth - 2\footnotemargin}
  %   \tiny
  %   \textcopyright\ \@copyrightyear\ %
  %   \ifx\@copyrightclause\@empty%
  %     \textcolor{red}{Author: Please fill in the \string\copyrightclause\space macro}%
  %   \else\@copyrightclause%
  %   \fi
  % \end{minipage}
  % \\
  \begin{minipage}[c]{\ccLogoWidth}
    \doclicenseImage[imagewidth=\ccLogoWidth]
  \end{minipage}
  \nobreak\enskip
  \begin{minipage}[c]{\linewidth - \ccLogoWidth - 2\footnotemargin}
    \tiny
    \textcopyright\ \@copyrightyear\ %
    \ifx\@copyrightclause\@empty%
      \doclicenseText
      % \textcolor{red}{Author: Please fill in the \string\copyrightclause\space macro}%
    \else\@copyrightclause%
    \fi
  \end{minipage}

}

\RequirePackage{calc}

% \def\@ceurLogoLine{%
%   % set width of ceur-ws logo equals to width of cc-by logo
%   \setbox\@tempboxa\hbox{\includegraphics[height=\baselineskip,clip]{cc-by}}%
%   \ccLogoWidth=\dimexpr\wd\@tempboxa
%   \setbox\@tempboxa\hbox{\includegraphics[width=\ccLogoWidth,clip]{ceur-ws-logo}}
%   \@rightskip\@flushglue \rightskip\@rightskip
%   % \hangindent\dimexpr\wd\@tempboxa+0.5em\relax
%   \begin{minipage}[c]{\ccLogoWidth}
%     \href{https://ceur-ws.org}%
%     % {\lower\baselineskip\hbox{\unhcopy\@tempboxa}}\enskip
%     {\hbox{\unhcopy\@tempboxa}}
%   \end{minipage}
%   \nobreak\enskip
%   \begin{minipage}[c]{\linewidth - \ccLogoWidth - 2\footnotemargin}
%     {CEUR~Workshop~Proceedings~(\href{https://ceur-ws.org}{CEUR-WS.org})}%
%   \end{minipage}
% }

\seq_new:N \g_ceur_logonote_seq

\NewDocumentCommand \logonote { m } {
  \group_begin:
  \seq_gput_right:Nn \g_ceur_logonote_seq
  {
    \tex_def:D \thefootnote { }
    \footnotetext{%
      \raggedright
      \hspace*{-\parindent}
      % \hspace*{-\labelsep}
      \hspace*{-\footnotemargin}
      #1}
  }
  \group_end:
}

\newcommand \printlogonotes { \seq_use:Nn \g_ceur_logonote_seq { \par } }

%
% Print all footnotes in the title page
%

\bool_new:N \g_ceur_longmktitle_bool
\int_new:N \g_ceur_jtype_int
\int_new:N \g_ceur_blind_int

\NewDocumentCommand \printFirstPageNotes { } {
  \bool_if:NTF \g_ceur_longmktitle_bool {
    \tex_let:D \columnwidth = \textwidth
  } { }
  \int_compare:nTF { \g_ceur_jtype_int > 5 } {
    \ceuraddress
  } { }
  \printnonumnotes
  \printtnotes
  \bool_if:NTF \g_ceur_blind_bool {
  } {
    \printcornotes
    \printfnotes
    \printmaltese
    \printaddrinfoot
    \printemails
    \printurls
    \printorcid
    \printfacebook
    \printtwitter
    \printgplus
    \printlinkedin
  }
  \printlogonotes
  \bool_if:NTF \g_ceur_longmktitle_bool {
    \if@twocolumn
      \tex_let:D \columnwidth = \Columnwidth \fi
  } { }
  \normalcolor
}

%
% Date History
%
\tl_new:N \g_ceur_recd_tl
\tl_new:N \g_ceur_accd_tl
\tl_new:N \g_ceur_revd_tl
\tl_new:N \g_ceur_pub_online_tl
\tl_new:N \g_ceur_pub_print_tl

\cs_new:Npn \date_parse:n #1 { \date_parse_aux:w #1 \q_stop }
\cs_new:Npn \date_parse_aux:w #1 / #2 / #3 \q_stop
{ <do something with the date> }

\NewDocumentCommand \received { m }
    { \tl_gput_right:Nn \g_ceur_recd_tl { #1 } }
\NewDocumentCommand \accepted { m }
    { \tl_gput_right:Nn \g_ceur_accd_tl { #1 } }
\NewDocumentCommand \revised { m }
    { \tl_gput_right:Nn \g_ceur_revd_tl { #1 } }
\NewDocumentCommand \published { O{} m }
{
  \tl_if_eq:nnTF { #1 } { online }
  { \tl_if_gput_right:Nn \g_ceur_pub_online_tl { #2 } }
  { \tl_if_gput_right:Nn \g_ceur_pub_print_tl { #2 } }
}

%
% Verse/Recto
%
\tl_new:N \l_ceur_verso_tl
\tl_new:N \l_ceur_recto_tl

\NewDocumentCommand \verso { m }
{ \tl_set:Nn \l_ceur_verso_tl { #1 } }
\NewDocumentCommand \recto { m }
{ \tl_set:Nn \l_ceur_recto_tl { #1 } }

%
% Maketitle
%

\newcounter{au}
\newcounter{cnote}
\newcounter{tnote}
\newcounter{fnote}
\newcounter{aff}

\cs_new:Nn \__reset_title_counters:
{
  \setcounter{cnote}{0}
  \setcounter{fnote}{0}
  \setcounter{tnote}{0}
  \setcounter{footnote}{0}
}

\keys_define:nn { ceur / mktitle }
{
  blind        .bool_gset:N     = \g_ceur_blind_bool        ,
  footer       .multichoice:,
       footer/default  .tl_gset:N  = \g_ceur_footer_default_tl ,
       footer/custom   .tl_gset:N  = \g_ceur_footer_custom_tl  ,
  longtitle     .bool_gset:N    = \g_ceur_longtitle_bool    ,
  longabstract  .bool_gset:N    = \g_ceur_longtitle_bool    ,
  breakafter    .clist_gset:N   = \g_ceur_breakafter_clist  ,
  nologo        .bool_gset:N    = \g_ceur_nologo_bool       ,
}

\bool_new:N \g_ceur_breakafter_title_bool
\bool_new:N \g_ceur_breakafter_auaff_bool
\bool_new:N \g_ceur_breakafter_abstract_bool

\NewDocumentCommand \processbreakafter { }
{
  \clist_if_empty:NTF \g_ceur_breakafter_clist { }
  {
    \clist_map_inline:Nn \g_ceur_breakafter_clist
    { \bool_gset_true:c { g_ceur_breakafter_##1_bool } }
  }
}

\NewDocumentCommand \pprintMaketitle { O{} }
{
  \tl_if_blank:nTF { #1 } { }
  { \keys_set:nn { ceur / mktitle } { #1 } }
  \processbreakafter
  \clearpage
  \__reset_title_counters:
  \tex_def:D \baselinestretch { 1 }
  \printFirstPageNotes
  \thispagestyle{pprintTitle}%
  \group_begin:
  \@title
  \group_end:
  \bool_if:NTF \g_ceur_breakafter_title_bool
  { \newpage } { }
  %
  \bool_if:NTF \g_ceur_blind_bool
  { \vspace* { 10 mm } }
  {
    \group_begin:
    \normalsize \ceurauthors \par
    \ceurcollab \par
    \footnotesize \itshape \ceuraddress \par \vskip36pt
    \group_end:
    \bool_if:NTF \g_ceur_breakafter_auaff_bool
    { \newpage } { }
  }
  %
  \printabsbox
  \printkeybox
  \bool_if:NTF \g_ceur_breakafter_abstract_bool
  { \newpage } { }
  %
  \setcounter{footnote}{\c@fnote}
  \tex_gdef:D \thefootnote { \arabic{footnote} }
  \tex_def:D \baselinestretch { \@blstr }
  \normalfont \normalsize
}

\NewDocumentCommand \MaketitleBox { } {
  \tex_def:D \baselinestretch{1}
  \group_begin:
  \@title
  \group_end:
  %
  \bool_if:NTF \g_ceur_blind_bool {
    \vspace* { 10 mm }
  } {
    \group_begin:
    \normalsize \ceurauthors \par
    \ceurcollab \par
    \footnotesize \itshape \ceuraddress \par
    \group_end:
    \bool_if:NTF \g_ceur_breakafter_auaff_bool
    { \newpage } { }
  }
  % \printFirstPageNotes
  %
  \dashrule{0pt}{3pt}
  \begin{Abstract}
    \noindent \ignorespaces
    \file_if_exist:nT { \jobname.abs } { \file_input:n { \jobname.abs } }
  \end{Abstract}
  \dashrule{6pt}{3pt}
  \bool_if:NTF \g_ceur_breakafter_abstract_bool
  { \newpage } { }
}

\box_new:N \g_ceur_notes_box
\box_new:N \g_ceur_front_box
\cs_set:Npn \__fn_text:n #1
{ \group_begin:\vbox_top:n { \footnotesize #1 } \group_end:\par}

\NewDocumentCommand \LongMaketitleBox { }
{
  \vbox_gset:Nn \g_ceur_front_box
  {
    \tex_def:D \baselinestretch{1}
    \group_begin:
    \@title
    \group_end:
    %
    \group_begin:
    \normalsize \ceurauthors \par
    \ceurcollab \par
    \footnotesize \itshape \ceuraddress \par
    \group_end:
  %
  \dashrule{0pt}{3pt}
  \begin{Abstract}
    \noindent \ignorespaces
    \file_if_exist:nT { \jobname.abs } { \file_input:n { \jobname.abs } }
  \end{Abstract}
  \dashrule{3pt}{3pt}
  }
  \vbox_gset:Nn \g_ceur_notes_box
  {  \cs_set_eq:NN \footnotetext \__fn_text:n  \printFirstPageNotes }
   \dim_gset:Nn \g_tmpb_dim { \box_ht:N \g_ceur_notes_box }
   % \iow_term:x { ...~[ht: \dim_use:N \g_tmpb_dim  ] }
   \dim_gadd:Nn \g_tmpb_dim { \box_dp:N \g_ceur_notes_box }
   % \iow_term:x { ...~[ht+dp: \dim_use:N \g_tmpb_dim  ] }
   \ifbool{sc}{\dim_gadd:Nn \g_tmpb_dim { 12pt } } { }

}

\NewDocumentCommand \ProcessLongTitleBox { }
{
  % \vbox_gset:Nn \g_ceur_notes_box
  % {  \cs_set_eq:NN \footnotetext \__fn_text:n \printFirstPageNotes }
  %  \dim_gset:Nn \g_tmpb_dim { \box_ht:N \g_ceur_notes_box }
  % % \iow_term:x { ...~[ht: \dim_use:N \g_tmpb_dim  ] }
  %  \dim_gadd:Nn \g_tmpb_dim { \box_dp:N \g_ceur_notes_box }
  % % \iow_term:x { ...~[ht+dp: \dim_use:N \g_tmpb_dim  ] }
  %
  \dim_gset:Nn \g_tmpa_dim { \textheight }
%  \vbox_unpack:N \g_ceur_notes_box
  % \iow_term:x { ...~[tmpa:~ \dim_use:N \g_tmpa_dim ] }
  % \dim_gsub:Nn \g_tmpa_dim { \box_ht:N \g_ceur_notes_box }
  % \iow_term:x { ...~[tmpa-noteht:~ \dim_use:N \g_tmpa_dim ] }
  % \dim_gsub:Nn \g_tmpa_dim { \box_dp:N \g_ceur_notes_box }
  % \iow_term:x { ...~[tmpa-notedp:~ \dim_use:N \g_tmpa_dim ] }
  \dim_gsub:Nn \g_tmpa_dim { \g_tmpb_dim }
  \vbox_set_split_to_ht:NNn \g_tmpb_box \g_ceur_front_box { \g_tmpa_dim }
  \noindent \vbox_unpack_clear:N \g_tmpb_box
  \printFirstPageNotes
  \dim_gzero:N \g_tmpa_dim
  \dim_gset:Nn \g_tmpa_dim { \box_ht:N \g_ceur_front_box }
  % \iow_term:x { ...~[tmpa-ht:~ \dim_use:N \g_tmpa_dim ] }
  \dim_gadd:Nn \g_tmpa_dim { \box_dp:N \g_ceur_front_box }
  % \iow_term:x { ...~[tmpa-ht+dp:~ \dim_use:N \g_tmpa_dim ~+~\the\textheight] }
  \dim_compare:nNnTF { \dim_use:N \g_tmpa_dim } > { \the\textheight }
  {
    \vbox_set_split_to_ht:NNn \g_tmpb_box \g_ceur_front_box { \textheight }
    \vbox_unpack_clear:N \g_tmpb_box
    \ifbool{dc}
    { \twocolumn[{\vbox_unpack_clear:N \g_ceur_front_box}] }
    { \vbox_unpack_clear:N \g_ceur_front_box }
  }
  {
    \ifbool{dc}
    { \twocolumn[{\vbox_unpack_clear:N \g_ceur_front_box}] }
    { \vbox_unpack_clear:N \g_ceur_front_box }
  }
 \normalcolor \normalfont
}
\ExplSyntaxOff

%
% Headings
%
\def\@seccntDot{.}
\def\@seccntformat#1{\csname the#1\endcsname\@seccntDot\hskip 0.5em}

\newdimen\paraindent     \paraindent=\parindent
\newdimen\subparaindent  \subparaindent=\parindent
\def\ssssparaindent{}
\def\sectionfont{\rmfamily\fontsize{12pt}{14pt}%
  \bfseries}
\def\ssectionfont{\rmfamily\fontsize{11pt}{13pt}%
  \bfseries\selectfont}
\def\sssectionfont{\rmfamily\fontsize{10.5pt}{12pt}%
  \fontseries{b}\fontshape{it}\selectfont}
\def\ssssectionfont{\rmfamily\fontsize{11pt}{10pt}\itshape\selectfont}
\def\sssssectionfont{\rmfamily\fontsize{11pt}{10pt}\selectfont}%

\AtBeginDocument{\global\@afterindentfalse}

% \renewcommand\section{\@startsection{section}{1}{\z@}%
%     {15pt \@plus 3\p@ \@minus 3\p@}%
%     {4\p@}%
%     {%\let\@hangfrom\relax
%      \sectionfont\raggedright\hst[13pt]}}

% \renewcommand\subsection{\@startsection{subsection}{2}{\z@}%
%     {10pt \@plus 3\p@ \@minus 2\p@}%
%     {.1\p@}%
%     {%\let\@hangfrom\relax
%      \ssectionfont\raggedright }}

% \renewcommand\subsubsection{\@startsection{subsubsection}{3}{\z@}%
%     {10pt \@plus 1\p@ \@minus .3\p@}%
%     {.1\p@}%
%     {%\let\@hangfrom\relax
%      \sssectionfont\raggedright}}

% \renewcommand\paragraph{\@startsection{paragraph}{4}{\parindent}%
%     {10pt \@plus0.01pt \@minus0.01pt}%
%     {-6pt}%
%     {\ssssparaindent%
%      \ssssectionfont\itshape\raggedright}}

% \renewcommand\subparagraph{\@startsection{subparagraph}{5}{\parindent}%
%     {0pt \@plus0.1pt \@minus0.1pt}%
%     {-6pt}%
%     {\hspace*{\subparaindent}
%      \sssssectionfont\raggedright}}

\def\thesubsection{\thesection.\arabic{subsection}}
\def\thesubsubsection{\thesubsection.\arabic{subsubsection}}

%
% Sundry lengths
%
\def\xstrut#1#2{\vrule height#1 depth #2 width\z@}
\def\hstrut#1{\vrule height#1 depth \z@ width 0pt}
\def\dstrut#1{\vrule height0pt depth#1 width 0pt}
\def\hst[#1]{\vrule height#1 depth \z@ width \z@}
\def\dst[#1]{\vrule height0pt depth#1 width 0pt}
\def\xst[#1][#2]{\vrule height#1 depth #2 width\z@}

\def\lastpage{100}

\AtEndDocument{%
%   \clearpage
   \immediate\write\@auxout{\string\csxdef{lastpage}{\thepage}}
}

\ExplSyntaxOn

%
% pagestyle
%

\RequirePackage{scrlayer-scrpage}
\clearpairofpagestyles

\setkomafont{pageheadfoot}{\sffamily\small}
% \setkomafont{pagehead}{\sffamily\small}

\bool_if:NTF \g_ceur_hf_bool {
  \KOMAoptions{headsepline}
  % \ofoot[Page~ \thepage {} ~of~ \lastpage]{Page~ \thepage {} ~of~ \lastpage}
  % \ifoot[\__short_authors: :~ { \rmfamily \itshape CEUR~Workshop~Proceedings}]{\__short_authors: :~ { \rmfamily \itshape CEUR~Workshop~Proceedings}}
  % \ohead[]{\__short_title:}
  \cfoot[\thepage]{\thepage}
  \ohead[]{\firstpage--\lastpage}
  \ihead[]{\__short_authors:{} ~ { \rmfamily \itshape CEUR~Workshop~Proceedings}}
}{ }

% \newcommand{\hffont}{\sffamily\small}

% \RequirePackage{scrlayer-fancyhdr}

% \fancypagestyle{first}{%
%   \fancyhf{}%
%   \renewcommand{\headrulewidth}{\z@}%
%   \renewcommand{\footrulewidth}{\z@}%
%   \fancyfoot[R]{\hffont Page~ \thepage {} ~of~ \lastpage}%
%   \fancyfoot[L]{\hffont \__short_authors: :~ { \rmfamily \itshape CEUR~Workshop~Proceedings}}%
% }

% \fancypagestyle{standard}{%
%   \fancyhf{}%
%   \renewcommand{\headrulewidth}{\z@}%
%   \renewcommand{\footrulewidth}{\z@}%
%   \fancyfoot[R]{\hffont Page~ \thepage {} ~of~ \lastpage}%
%   \fancyfoot[L]{\hffont \__short_authors: :~ { \rmfamily \itshape CEUR~Workshop~Proceedings}}%
%   \fancyhead[L]{\hffont \__short_title:}%
% }

\cs_new:Npn \__first_footerline: {
  \group_begin:
  \small \sffamily
  \__short_authors: :~
  { \rmfamily \itshape CEUR~Workshop~Proceedings }
  \group_end:
}

\cs_new:Npn \__first_head: {
  \parbox[t]{\textwidth}
  {
    \color{black!20}
    \rule{\textwidth}{0pt}
  }
}

\cs_new:Npn \__first_foot: {
  \parbox[t]{\textwidth} {
    % \rule{\textwidth}{.2pt}\\
    \sffamily\small
    \__first_footerline:
    \hfill Page~ \thepage {} ~of~ \lastpage
  }
}

\cs_new:Npn \__ceur_head: {
  \parbox{\textwidth} {
    \sffamily\small\centering
    \__short_title:
  }
}

\cs_new:Npn \__ceur_foot: {
  \parbox[t]{\textwidth} {
    % \rule{\textwidth}{.2pt}\\
    \sffamily\small
    \__first_footerline:
    \hfill Page~\thepage {}~of~ \lastpage
  }
}

% \newcommand \ps@first {
%   \cs_set_eq:NN \@oddhead \__first_head:
%   \cs_set_eq:NN \@evenhead \__first_head:
%   \cs_set_eq:NN \@evenfoot \__first_foot:
%   \cs_set_eq:NN \@oddfoot \__first_foot:
% }

% \newcommand \ps@ceur {
%   \cs_set_eq:NN \@oddhead \__ceur_head:
%   \cs_set_eq:NN \@evenhead \__ceur_head:
%   \cs_set_eq:NN \@evenfoot \__ceur_foot:
%   \cs_set_eq:NN \@oddfoot \__ceur_foot:
% }

% \ps@ceur

%
% Floats
%

\def\topfraction{.9}
\def\bottomfraction{.9}
\setcounter{topnumber}{4}
\setcounter{bottomnumber}{3}
\setcounter{totalnumber}{5}
\renewcommand\textfraction{.1}
\renewcommand\floatpagefraction{.9}
\setcounter{dbltopnumber}{2}
\renewcommand\dbltopfraction{.9}
\renewcommand\dblfloatpagefraction{.95}
\newdimen \FullWidth
\FullWidth=\textwidth

\newcolumntype{L}{@{\extracolsep{\fill}}l}
\newcolumntype{R}{@{\extracolsep{\fill}}r}
\newcolumntype{C}{@{\extracolsep{\fill}}c}

\cs_gset_eq:NN \thead  \toprule
\cs_gset_eq:NN \endthead  \midrule
\cs_gset_eq:NN \tabref  \ref

\dim_new:N \l_tbl_width_dim
\dim_set:Nn \l_tbl_width_dim { \linewidth }

\cs_new:Npn \__make_tbl_caption:nn #1#2
{
  \l_tbl_align_tl
  \skip_vertical:N \l_tbl_abovecap_skip
  % \bool_if:NTF \g_tbl_full_bool
  % {
  %  \color{scolor!70}\rule{\FullWidth}{2pt}\normalcolor\\
  % }
  % { \color{scolor!70}\rule{\tblwidth}{2pt}\normalcolor\\ }
  % \fboxsep=4pt
  % \colorbox{white}
  {\parbox{ \dimexpr(\l_tbl_width_dim)}
    {\rightskip=0pt\sffamily\small\textbf{\color{scolor}#1}\par#2\par\vskip4pt }}
  \skip_vertical:N \l_tbl_belowcap_skip
}

\keys_define:nn { ceur / tbl } {
  width     .dim_set:N   =  \l_tbl_width_dim ,
  pos       .tl_set:N    =  \l_tbl_pos_tl ,
  cols      .tl_set:N    =  \l_tbl_cols_tl ,
  align     .tl_set:N    =  \l_tbl_align_tl,
  abovecap  .skip_set:N  =  \l_tbl_abovecap_skip ,
  belowcap  .skip_set:N  =  \l_tbl_belowcap_skip ,
  abovetbl  .skip_set:N  =  \l_tbl_abovetbl_skip ,
  belowtbl  .skip_set:N  =  \l_tbl_belowtbl_skip ,
  full      .bool_gset:N =  \g_tbl_full_bool ,
  unknown   .code:n      =  \tl_set:Nx \l_tbl_pos_tl { \l_keys_key_str },
}

\cs_set:Npn \__reset_tbl: {
  \tl_set:Nx \l_tbl_pos_tl { t }
  \tl_set:Nx \l_tbl_cols_tl { 1 }
  \tl_set:Nn \l_tbl_align_tl { \centering }
  \skip_set:Nn \l_tbl_abovecap_skip { 6pt }
  \skip_set:Nn \l_tbl_belowcap_skip { 0pt }
  \skip_set:Nn \l_tbl_abovetbl_skip { 6pt }
  \skip_set:Nn \l_tbl_belowtbl_skip { 6pt }
}

\RenewDocumentEnvironment { table } { O{} } {
  \__reset_tbl:
  \bool_gset_false:N \g_tbl_full_bool
  \dim_set:Nn \l_tbl_width_dim { \linewidth }
  \keys_set:nn { ceur / tbl } { #1 }
  \csxdef{fps@table}{\l_tbl_pos_tl}
  \csgdef{tblwidth}{\dim_use:N \l_tbl_width_dim}
  \cs_set_eq:NN \@makecaption \__make_tbl_caption:nn
  \@float{table}
  \l_tbl_align_tl
  \sffamily\small
}
{ \end@float }


\RenewDocumentEnvironment { table* } { O{width=\FullWidth} } {
  \__reset_tbl:
  \bool_gset_true:N \g_tbl_full_bool
  \dim_set:Nn \l_tbl_width_dim { \FullWidth }
  \keys_set:nn { ceur / tbl } { #1 }
  \csxdef{fps@table}{\l_tbl_pos_tl}
  \csgdef{tblwidth}{\dim_use:N \l_tbl_width_dim}
  \cs_set_eq:NN \@makecaption \__make_tbl_caption:nn
  \@dblfloat{table}
  \l_tbl_align_tl
  \sffamily\small
  % \leftskip=-\FullWidth
}
{ \end@dblfloat }

\dim_new:N \l_fig_width_dim
\dim_set:Nn \l_fig_width_dim { \linewidth }

\cs_new:Npn \__make_fig_caption:nn #1#2 {
  \l_fig_align_tl
  \skip_vertical:N \l_fig_abovecap_skip
  % \bool_if:NTF \g_fig_full_bool
  % { \skip_horizontal:n { -\FullWidth } } { }
  \parbox{ \l_fig_width_dim }
  {\rightskip=0pt\sffamily\small\textbf{\color{scolor}#1:}~#2\par }
  \skip_vertical:N \l_fig_belowcap_skip
}

\keys_define:nn { ceur / fig } {
  width     .dim_set:N   =  \l_fig_width_dim ,
  pos       .tl_set:N    =  \l_fig_pos_tl ,
  cols      .tl_set:N    =  \l_fig_cols_tl ,
  align     .tl_set:N    =  \l_fig_align_tl,
  abovecap  .skip_set:N  =  \l_fig_abovecap_skip ,
  belowcap  .skip_set:N  =  \l_fig_belowcap_skip ,
  abovefig  .skip_set:N  =  \l_fig_abovefig_skip ,
  belowfig  .skip_set:N  =  \l_fig_belowfig_skip ,
  full      .bool_gset:N =  \g_fig_full_bool ,
  unknown   .code:n      =  \tl_set:Nx \l_fig_pos_tl { \l_keys_key_str },
}

\cs_set:Npn \__reset_fig: {
  \tl_set:Nx \l_fig_pos_tl { t }
  \tl_set:Nx \l_fig_cols_tl { 1 }
  \tl_set:Nn \l_fig_align_tl { \raggedleft }
  \skip_set:Nn \l_fig_abovecap_skip { 6pt }
  \skip_set:Nn \l_fig_belowcap_skip { 6pt }
  \skip_set:Nn \l_fig_abovefig_skip { 6pt }
  \skip_set:Nn \l_fig_belowfig_skip { 6pt }
}

\RenewDocumentEnvironment { figure } { O{} } {
  \__reset_fig:
  \bool_gset_false:N \g_fig_full_bool
  \dim_set:Nn \l_fig_width_dim { \linewidth }
  \keys_set:nn { ceur / fig } { #1 }
  \csxdef{fps@figure}{\l_fig_pos_tl}
  \csgdef{figwidth}{\dim_use:N \l_fig_width_dim}
  \cs_set_eq:NN \@makecaption \__make_fig_caption:nn
  \@float{figure}
  \l_fig_align_tl
  \sffamily\small
}{ \end@float }

\RenewDocumentEnvironment { figure* } { O{width=\textwidth} } {
  \__reset_fig:
  \bool_gset_true:N \g_fig_full_bool
  \dim_set:Nn \l_fig_width_dim { \FullWidth }
  \keys_set:nn { ceur / fig } { #1 }
  \csxdef{fps@figure}{\l_fig_pos_tl}
  \csgdef{figwidth}{\dim_use:N \l_fig_width_dim}
  \cs_set_eq:NN \@makecaption \__make_fig_caption:nn
  \@dblfloat{figure}
  \l_fig_align_tl
  \sffamily\small
  % \leftskip=-\FullWidth
}
{ \end@dblfloat }

%
% wrapped figure
%
\RequirePackage{wrapfig}

\dim_new:N \l_wrap_figwidth_dim
\dim_new:N \l_wrap_fighspace_dim
\dim_new:N \l_wrap_figvspace_dim
\dim_new:N \l_wrap_fighcorr_dim
\dim_new:N \l_wrap_figvcorr_dim
\dim_new:N \l_above_bio_dim
\int_new:N \l_wrap_figlcorr_int
\int_new:N \l_wrap_figlines_int
\tl_new:N  \l_wrap_figfile_tl

\NewDocumentCommand \wfigwidth { m }
  { \dim_set:Nn \l_wrap_figwidth_dim { #1 } }
\NewDocumentCommand \wfighspace { m }
  { \dim_set:Nn \l_wrap_fighspace_dim { #1 } }
\NewDocumentCommand \wfigvspace { m }
  { \dim_set:Nn \l_wrap_figvspace_dim { #1 } }
\NewDocumentCommand \wfighcorr { m }
  { \dim_set:Nn \l_wrap_fighcorr_dim { #1 } }
\NewDocumentCommand \wfigvcorr { m }
  { \dim_set:Nn \l_wrap_figvcorr_dim { #1 } }
\NewDocumentCommand \addfiglines { m }
  { \int_set:Nn \l_wrap_figlcorr_int { #1 } }
\NewDocumentCommand \abovebioskip { m }
  { \dim_set:Nn \l_above_bio_dim { #1 } }

\cs_new:Nn \__fig_defaults: {
  \wfigwidth  { 25.5mm }
  \wfighspace { 0mm }
  \wfigvspace { 0mm }
  \wfighcorr  { 0pt }
  \wfigvcorr  { -12pt }
  \wfigvcorr  { 0pt }
  \abovebioskip { 12pt }
  \tl_set:Nn  \l_wrap_figpos_tl { l }
  \int_set:Nn \l_wrap_figlines_int { 3 }
  \int_set:Nn \l_wrap_figlcorr_int { 1 }
  \tl_clear:N \l_wrap_figcap_tl
}

\__fig_defaults:

\keys_define:nn { wrap / fig } {
  width    .dim_set:N    =  \l_wrap_figwidth_dim ,
  hspace   .dim_set:N    =  \l_wrap_fighspace_dim ,
  vspace   .dim_set:N    =  \l_wrap_figvspace_dim ,
  hcorr    .dim_set:N    =  \l_wrap_fighcorr_dim ,
  vcorr    .dim_set:N    =  \l_wrap_figvcorr_dim ,
  lcorr    .int_set:N    =  \l_wrap_figlcorr_int ,
  pos      .tl_set:N     =  \l_wrap_figpos_tl ,
  lines    .int_set:N    =  \l_wrap_figlines_int ,
  cap      .tl_set:N     =  \l_wrap_figcap_tl ,
}

\cs_new:Npn \__find_fig_height:n #1 {
  \box_clear:N  \g_tmpa_box
  \hbox_gset:Nn \g_tmpa_box
  { \includegraphics [ width = \l_wrap_figwidth_dim ] { #1 } }
  \dim_zero:N \l_tmpa_dim
  \dim_set:Nn \l_tmpa_dim { \box_ht:N \g_tmpa_box }
  \dim_add:Nn \l_tmpa_dim { \box_dp:N \g_tmpa_box }
  \fp_set:Nn  \l_tmpa_fp  { \dim_to_fp:n { \l_tmpa_dim } }
  \fp_set:Nn  \l_tmpb_fp  { \dim_to_fp:n { \baselineskip } }
  %
  \fp_set:Nn \l_wrap_figlines_fp
  { \fp_eval:n { ( \l_tmpa_fp / \l_tmpb_fp )  + .5 } }
  \int_set:Nn \l_wrap_figlines_int
  { \fp_to_int:N \l_wrap_figlines_fp }
  %
  \iow_term:x { ...~wr-fig:~[BL:~\the\baselineskip] ~ ...}
  \iow_term:x { ...~wr-fig:~[LINE-FP:~ \fp_use:N \l_wrap_figlines_fp]~ ...}
  \iow_term:x { ...~wr-fig:~[LINE-INT:~ \int_use:N \l_wrap_figlines_int]~ ...}
}

\newbox \l_bio_text_box

\NewDocumentCommand \WrapFigure { o m } {
  \__fig_defaults:
  \IfNoValueTF { #1 } { } { \keys_set:nn { wrap / fig } { #1 } }
  \stepcounter { ca_biography_ctr }
  \__find_fig_height:n { #2 }
  \dim_zero:N \l_tmpb_dim
  \dim_set:Nn \l_tmpb_dim
  { \l_wrap_figwidth_dim + \l_wrap_fighspace_dim }
  \int_gadd:Nn \l_wrap_figlines_int { \int_use:N \l_wrap_figlcorr_int }
  \setlength { \columnsep } { 5pt }
  \setlength { \intextsep } { 0pt }
  % \mbox{}
  \ifbool { dc } {
    \xdef\Columnwidth{238.25pt}
  }{
    \xdef\Columnwidth{\the\textwidth}
  }
  \ifcsundef { cabio\theca_biography_ctr lines }
  {
    \setbox \l_bio_text_box = \vbox \bgroup
    \hsize = \dimexpr ( \Columnwidth - 72.28pt )
  }
  {
    \ifbool { dc } {
      \int_gset:Nn \l_wrap_figlines_int
      { \csuse { cabio\theca_biography_ctr lines } }
    } { }
    \skip_vertical:N \l_above_bio_dim
    \begin{wrapfigure}[\int_use:N \l_wrap_figlines_int]
      { \l_wrap_figpos_tl }
      [ \dim_use:N \l_wrap_fighcorr_dim ]
      { \dim_use:N \l_tmpb_dim }
      % \skip_vertical:N \l_wrap_figvcorr_dim
      \includegraphics[width=\l_wrap_figwidth_dim]{#2}
    \end{wrapfigure}
    \setbox \l_bio_text_box = \vbox \bgroup
    \hsize = \dimexpr ( \Columnwidth )
  }
}

\cs_set:Nn \__fwidth: { 1in }
\cs_set:Nn \__fpos: { l }

%
% short authors/title
%

\tl_new:N \__short_authors:
\newcommand\shortauthors[1]{ \cs_gset:Nn \__short_authors: { #1 } }

\tl_new:N \__short_title:
\newcommand\shorttitle[1]{ \cs_gset:Nn \__short_title: { #1 } }

\newcounter { ca_biography_ctr }
\newbool { cas_no_pic_bio }
\boolfalse { cas_no_pic_bio }

\NewDocumentCommand \bio { O{} m }
{
  \global \boolfalse { cas_no_pic_bio }
  \casbiographyfont
  \par \medskip  \tl_set:Nn \l_tmpa_tl { #2 }
  \tl_if_empty:NTF \l_tmpa_tl
  { \global \booltrue { cas_no_pic_bio } }
  { \WrapFigure [ #1 ]{ #2 } }
  \noindent \ignorespaces
}

\int_new:N \l_ca_temp_inta

\NewDocumentCommand \endbio { } {
 \ifbool{ cas_no_pic_bio } { } {
  \egroup
%  \fp_set:Nn \l_wrap_figlines_fp
%    { \fp_eval:n { ( ( \l_tmpa_fp +
%      \numexpr\dimexpr\the\ht\l_bio_text_box )
%      / \l_tmpb_fp )  + .5 } }
  \int_gset:Nn \l_ca_temp_inta
      { \numexpr\dimexpr(\the\ht\l_bio_text_box + 2\baselineskip )/
        \dimexpr\the\baselineskip }
  \iow_now:Nx \@auxout {
     \string\csgdef{cabio\theca_biography_ctr lines}
        { \int_use:N \l_ca_temp_inta } }
\mbox{}\vspace*{-4.5pt}\noindent
\unvbox \l_bio_text_box }
}

\let\casbiographyfont\relax

\NewDocumentEnvironment { biography } { o m }
{
  \IfValueTF { #1 }
  { \par\medskip \noindent \includegraphics[width=1in]{#1} }
  { }
  \par\smallskip
  \noindent \textbf{#2:}\enspace
}
{ }

\ExplSyntaxOff

%
% Customized Enumeration
%
\def\blstr#1{\gdef\@bslstr{#1}}
\def\@blstr{1}
\newdimen\leftMargin
\leftMargin=2em
\newtoks\@enLab  %\newtoks\@enfont
\def\@enQmark{?}
\def\@enLabel#1#2{%
  \edef\@enThe{\noexpand#1{\@enumctr}}%
  \@enLab\expandafter{\the\@enLab\csname the\@enumctr\endcsname}%
  \@enloop}
\def\@enSpace{\afterassignment\@enSp@ce\let\@tempa= }
\def\@enSp@ce{\@enLab\expandafter{\the\@enLab\space}\@enloop}
\def\@enGroup#1{\@enLab\expandafter{\the\@enLab{#1}}\@enloop}
\def\@enOther#1{\@enLab\expandafter{\the\@enLab#1}\@enloop}
\def\@enloop{\futurelet\@entemp\@enloop@}
\def\@enloop@{%
  \ifx A\@entemp         \def\@tempa{\@enLabel\Alph  }\else
  \ifx a\@entemp         \def\@tempa{\@enLabel\alph  }\else
  \ifx i\@entemp         \def\@tempa{\@enLabel\roman }\else
  \ifx I\@entemp         \def\@tempa{\@enLabel\Roman }\else
  \ifx 1\@entemp         \def\@tempa{\@enLabel\arabic}\else
  \ifx \@sptoken\@entemp \let\@tempa\@enSpace         \else
  \ifx \bgroup\@entemp   \let\@tempa\@enGroup         \else
  \ifx \@enum@\@entemp   \let\@tempa\@gobble          \else
                         \let\@tempa\@enOther
             \fi\fi\fi\fi\fi\fi\fi\fi
  \@tempa}
\newlength{\@sep} \newlength{\@@sep}
\setlength{\@sep}{.5\baselineskip plus.2\baselineskip
            minus.2\baselineskip}
\setlength{\@@sep}{.1\baselineskip plus.01\baselineskip
            minus.05\baselineskip}
\providecommand{\sfbc}{\rmfamily\upshape}
\providecommand{\sfn}{\rmfamily\upshape}
\def\@enfont{\ifnum \@enumdepth >1\let\@nxt\sfn \else\let\@nxt\sfbc \fi\@nxt}
\def\enumerate{%
   \ifnum \@enumdepth >3 \@toodeep\else
      \advance\@enumdepth \@ne
      \edef\@enumctr{enum\romannumeral\the\@enumdepth}\fi
   \@ifnextchar[{\@@enum@}{\@enum@}}
\def\@@enum@[#1]{%
  \@enLab{}\let\@enThe\@enQmark
  \@enloop#1\@enum@
  \ifx\@enThe\@enQmark\@warning{The counter will not be printed.%
   ^^J\space\@spaces\@spaces\@spaces The label is: \the\@enLab}\fi
  \expandafter\edef\csname label\@enumctr\endcsname{\the\@enLab}%
  \expandafter\let\csname the\@enumctr\endcsname\@enThe
  \csname c@\@enumctr\endcsname7
  \expandafter\settowidth
            \csname leftmargin\romannumeral\@enumdepth\endcsname
            {\the\@enLab\hskip\labelsep}%
  \@enum@}
\def\@enum@{\list{{\@enfont\csname label\@enumctr\endcsname}}%
           {\usecounter{\@enumctr}\def\makelabel##1{\hss\llap{##1}}%
     \ifnum \@enumdepth>1\setlength{\topsep}{\@@sep}\else
           \setlength{\topsep}{\@sep}\fi
     \ifnum \@enumdepth>1\setlength{\itemsep}{0pt plus1pt minus1pt}%
      \else \setlength{\itemsep}{\@@sep}\fi
     %\setlength\leftmargin{\leftMargin}%%%{1.8em}
     \setlength{\parsep}{0pt plus1pt minus1pt}%
     \setlength{\parskip}{0pt plus1pt minus1pt}
                   }}

\def\endenumerate{\par\ifnum \@enumdepth >1\addvspace{\@@sep}\else
           \addvspace{\@sep}\fi \endlist}

\def\sitem{\@noitemargtrue\@item[\@itemlabel *]}

\def\itemize{\@ifnextchar[{\@Itemize}{\@Itemize[]}}

\def\@Itemize[#1]{%
  \def\next{#1}%
  \ifnum \@itemdepth >\thr@@\@toodeep\else
    \advance\@itemdepth\@ne
    \ifx\next\@empty\else\expandafter\def\csname
      labelitem\romannumeral\the\@itemdepth\endcsname{#1}\fi%
    \edef\@itemitem{labelitem\romannumeral\the\@itemdepth}%
    \expandafter\list\csname\@itemitem\endcsname
    {\def\makelabel##1{\hss\llap{##1}}}%
  \fi
  \setlength{\itemsep}{\@@sep}
  \setlength{\parsep}{0pt plus1pt minus1pt}%
  \setlength{\parskip}{0pt plus1pt minus1pt}
}

%
% Customized theorem
% (non-italic enunciations)
%

\def\newdefinition#1{%
  \@ifnextchar[{\@odfn{#1}}{\@ndfn{#1}}}%]
\def\@ndfn#1#2{%
  \@ifnextchar[{\@xndfn{#1}{#2}}{\@yndfn{#1}{#2}}}
\def\@xndfn#1#2[#3]{%
  \expandafter\@ifdefinable\csname #1\endcsname
    {\@definecounter{#1}\@newctr{#1}[#3]%
     \expandafter\xdef\csname the#1\endcsname{%
       \expandafter\noexpand\csname the#3\endcsname \@dfncountersep
          \@dfncounter{#1}}%
     \global\@namedef{#1}{\@dfn{#1}{#2}}%
     \global\@namedef{end#1}{\@enddefinition}}}
\def\@yndfn#1#2{%
  \expandafter\@ifdefinable\csname #1\endcsname
    {\@definecounter{#1}%
     \expandafter\xdef\csname the#1\endcsname{\@dfncounter{#1}}%
     \global\@namedef{#1}{\@dfn{#1}{#2}}%
     \global\@namedef{end#1}{\@enddefinition}}}
\def\@odfn#1[#2]#3{%
  \@ifundefined{c@#2}{\@nocounterr{#2}}%
    {\expandafter\@ifdefinable\csname #1\endcsname
    {\global\@namedef{the#1}{\@nameuse{the#2}}
  \global\@namedef{#1}{\@dfn{#2}{#3}}%
  \global\@namedef{end#1}{\@enddefinition}}}}
\def\@dfn#1#2{%
  \refstepcounter{#1}%
  \@ifnextchar[{\@ydfn{#1}{#2}}{\@xdfn{#1}{#2}}}
\def\@xdfn#1#2{%
  \@begindefinition{#2}{\csname the#1\endcsname}\ignorespaces}
\def\@ydfn#1#2[#3]{%
  \@opargbegindefinition{#2}{\csname the#1\endcsname}{#3}\ignorespaces}
\def\@dfncounter#1{\noexpand\arabic{#1}}
\def\@dfncountersep{.}
\def\@begindefinition#1#2{\trivlist
   \item[\hskip\labelsep{\bfseries #1\ #2.}]\upshape}
\def\@opargbegindefinition#1#2#3{\trivlist
      \item[\hskip\labelsep{\bfseries #1\ #2\ (#3).}]\upshape}
\def\@enddefinition{\endtrivlist}

\def\@begintheorem#1#2{\trivlist
  \let\baselinestretch\@blstr
   \item[\hskip \labelsep{\bfseries #1\ #2.}]\itshape}
\def\@opargbegintheorem#1#2#3{\trivlist
  \let\baselinestretch\@blstr
      \item[\hskip \labelsep{\bfseries #1\ #2\ (#3).}]\itshape}
%
% Unnumbered roman proofs
%
\def\newproof#1{%
  \@ifnextchar[{\@oprf{#1}}{\@nprf{#1}}}
\def\@nprf#1#2{%
  \@ifnextchar[{\@xnprf{#1}{#2}}{\@ynprf{#1}{#2}}}
\def\@xnprf#1#2[#3]{%
  \expandafter\@ifdefinable\csname #1\endcsname
    {\@definecounter{#1}\@newctr{#1}[#3]%
     \expandafter\xdef\csname the#1\endcsname{%
       \expandafter\noexpand\csname the#3\endcsname \@prfcountersep
          \@prfcounter{#1}}%
     \global\@namedef{#1}{\@prf{#1}{#2}}%
     \global\@namedef{end#1}{\@endproof}}}
\def\@ynprf#1#2{%
  \expandafter\@ifdefinable\csname #1\endcsname
    {\@definecounter{#1}%
     \expandafter\xdef\csname the#1\endcsname{\@prfcounter{#1}}%
     \global\@namedef{#1}{\@prf{#1}{#2}}%
     \global\@namedef{end#1}{\@endproof}}}
\def\@oprf#1[#2]#3{%
  \@ifundefined{c@#2}{\@nocounterr{#2}}%
    {\expandafter\@ifdefinable\csname #1\endcsname
    {\global\@namedef{the#1}{\@nameuse{the#2}}%
  \global\@namedef{#1}{\@prf{#2}{#3}}%
  \global\@namedef{end#1}{\@endproof}}}}
\def\@prf#1#2{%
  \refstepcounter{#1}%
  \@ifnextchar[{\@yprf{#1}{#2}}{\@xprf{#1}{#2}}}
\def\@xprf#1#2{%
  \@beginproof{#2}{\csname the#1\endcsname}\ignorespaces}
\def\@yprf#1#2[#3]{%
  \@opargbeginproof{#2}{\csname the#1\endcsname}{#3}\ignorespaces}
\def\@prfcounter#1{\noexpand\arabic{#1}}
\def\@prfcountersep{.}
\def\@beginproof#1#2{\trivlist\let\baselinestretch\@blstr
   \item[\hskip \labelsep{\scshape #1.}]\rmfamily}
\def\@opargbeginproof#1#2#3{\trivlist\let\baselinestretch\@blstr
      \item[\hskip \labelsep{\scshape #1\ (#3).}]\rmfamily}
\def\@endproof{\endtrivlist}
\newcommand*{\qed}{\hbox{}\hfill$\Box$}

\xspaceaddexceptions{]}

\ExplSyntaxOn

%%
%% Bibliography
%%

% \RequirePackage[numbers,sort&compress]{natbib}
\RequirePackage[numbers]{natbib}
\AtBeginDocument{\bibsep=0pt}

\bibliographystyle{elsarticle-num-names}
% \bibliographystyle{elsarticle-num}

%%
%% Fonts
%%

\ifpdftex
\RequirePackage[T1]{fontenc}
\fi

%% Main font
\file_if_exist:nTF { libertinus.sty }
{
  \RequirePackage{libertinus}
}{
  \iow_term:x { Libertinus fonts are not available }
}

%% Math font for pdfLaTeX
% \ifpdftex
% \file_if_exist:nTF { libertinust1math.sty }
% {
%   \RequirePackage{libertinust1math}
% }{
%   \iow_term:x { Libertinus math fonts are not available }
% }
% \fi

\ExplSyntaxOff

%%
%% Compatibility workaround
%%

%% Old font naming commands for Koma class

\DeclareOldFontCommand{\rm}{\normalfont\rmfamily}{\mathrm}
\DeclareOldFontCommand{\sf}{\normalfont\sffamily}{\mathsf}
\DeclareOldFontCommand{\tt}{\normalfont\ttfamily}{\mathtt}
\DeclareOldFontCommand{\bf}{\normalfont\bfseries}{\mathbf}
\DeclareOldFontCommand{\it}{\normalfont\itshape}{\mathit}
\DeclareOldFontCommand{\sl}{\normalfont\slshape}{\@nomath\sl}
\DeclareOldFontCommand{\sc}{\normalfont\scshape}{\@nomath\sc}

%%
%% Page geometry
%%

\RequirePackage{geometry}
\geometry{a4paper}
\geometry{%
  twoside=false,
  vmargin=1cm,
  hmargin=1in,
  centering,
  columnsep=2pc,
  heightrounded,
  includeheadfoot,
}

\endinput

%
% End of class 'ceurart'
%

%%% Local Variables:
%%% mode: latex
%%% TeX-master: t
%%% coding: utf-8-unix
%%% End:
