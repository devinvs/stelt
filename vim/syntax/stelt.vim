" Vim syntax file
" Language: Stelt
" Maintainer: Devin Vander Stelt

if exists("b:current_syntax")
  finish
endif

" Match operators
syn match steltOperator '[+-<>():=|]'

" Match an identifier
syn match steltIdent contained '[A-Za-z]\+'

" Match a typedef or typedecl

syn keyword steltKeywords extern
syn keyword steltKeywords type nextgroup=steltTypeDef,steltTypeDecl

syn match steltEquals '='
syn match steltColon ':'

syn match steltTypeDef '.*=' contained contains=steltTypeArgs,steltEquals nextgroup=steltType
syn match steltTypeDecl '.*:' contained contains=steltTypeArgs,steltColon nextgroup=steltType

syn region steltTypeArgs matchgroup=steltOperator start='<' end='>' contained contains=steltIdent

syn keyword steltBuiltinType contained str u8 u16 u32 u64 i8 i16 i32 i64
syn match steltType contained '.*$' contains=steltBuiltinType,steltTypeArgs,steltOperator,steltNamedType,steltTypeVar

syn match steltNamedType '[A-Z][A-Za-z]*' contained
syn match steltTypeVar '[a-z][A-Za-z]*' contained

" Match a function definition
syn match steltFunction '[A-Za-z]\+(.*)' contains=steltOperator,steltNum,steltString,steltIdent

syn region steltMultiExpr start="{" end="}" fold transparent contains=steltString,steltComment,steltNum

" Match a string, contains escape characters
syn match steltEscape contained '\\[n"t\\]'
syn region steltString start='"' end='"' skip='\\"' contained contains=steltEscape

" Match a number or float
syn match steltNum contained '-\?\d\+'
syn match steltNum contained '-\?\d\+\.\d\+'

" Match a single line comment, can contain TODO or FIXME
syn keyword steltTodo contained TODO FIXME
syn match steltComment "//.*$" contains=steltTodo

let b:current_syntax = "stelt"

hi def link steltComment        Comment
hi def link steltTodo           Todo
hi def link steltKeywords       Keyword
hi def link steltString         String
hi def link steltEscape         SpecialChar
hi def link steltNum            Number
hi def link steltTypeDecl       Function
hi def link steltTypeDef        Typedef
hi def link steltTypeOps        Operator
hi def link steltBuiltinType    Type
hi def link steltIdent          Identifier
hi def link steltOperator       Operator
hi def link steltFunction       Function
hi def link steltEquals         Operator
hi def link steltColon          Operator
hi def link steltNamedType      Type
hi def link steltTypeVar        Identifier
