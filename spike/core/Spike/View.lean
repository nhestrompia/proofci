import Aeneas
import ProofciJs

open Aeneas Aeneas.Std Result

def src.scale.joins160 (a : Js.Num) : Result Js.Num := do
  let t ← Result.ok ((Js.Num.mk (0) (of_decide_eq_true rfl) (of_decide_eq_true rfl)))
  let t_2 ← if a.val > 0 then
      let tmp1 ← Js.add t (Js.Num.mk (1) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_1 ← Result.ok (tmp1)
      Result.ok t_1
    else
      Result.ok t
  let t_4 ← if a.val > 1 then
      let tmp2 ← Js.add t_2 (Js.Num.mk (2) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_3 ← Result.ok (tmp2)
      Result.ok t_3
    else
      Result.ok t_2
  let t_6 ← if a.val > 2 then
      let tmp3 ← Js.add t_4 (Js.Num.mk (3) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_5 ← Result.ok (tmp3)
      Result.ok t_5
    else
      Result.ok t_4
  let t_8 ← if a.val > 3 then
      let tmp4 ← Js.add t_6 (Js.Num.mk (4) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_7 ← Result.ok (tmp4)
      Result.ok t_7
    else
      Result.ok t_6
  let t_10 ← if a.val > 4 then
      let tmp5 ← Js.add t_8 (Js.Num.mk (5) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_9 ← Result.ok (tmp5)
      Result.ok t_9
    else
      Result.ok t_8
  let t_12 ← if a.val > 5 then
      let tmp6 ← Js.add t_10 (Js.Num.mk (6) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_11 ← Result.ok (tmp6)
      Result.ok t_11
    else
      Result.ok t_10
  let t_14 ← if a.val > 6 then
      let tmp7 ← Js.add t_12 (Js.Num.mk (7) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_13 ← Result.ok (tmp7)
      Result.ok t_13
    else
      Result.ok t_12
  let t_16 ← if a.val > 7 then
      let tmp8 ← Js.add t_14 (Js.Num.mk (8) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_15 ← Result.ok (tmp8)
      Result.ok t_15
    else
      Result.ok t_14
  let t_18 ← if a.val > 8 then
      let tmp9 ← Js.add t_16 (Js.Num.mk (9) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_17 ← Result.ok (tmp9)
      Result.ok t_17
    else
      Result.ok t_16
  let t_20 ← if a.val > 9 then
      let tmp10 ← Js.add t_18 (Js.Num.mk (10) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_19 ← Result.ok (tmp10)
      Result.ok t_19
    else
      Result.ok t_18
  let t_22 ← if a.val > 10 then
      let tmp11 ← Js.add t_20 (Js.Num.mk (11) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_21 ← Result.ok (tmp11)
      Result.ok t_21
    else
      Result.ok t_20
  let t_24 ← if a.val > 11 then
      let tmp12 ← Js.add t_22 (Js.Num.mk (12) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_23 ← Result.ok (tmp12)
      Result.ok t_23
    else
      Result.ok t_22
  let t_26 ← if a.val > 12 then
      let tmp13 ← Js.add t_24 (Js.Num.mk (13) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_25 ← Result.ok (tmp13)
      Result.ok t_25
    else
      Result.ok t_24
  let t_28 ← if a.val > 13 then
      let tmp14 ← Js.add t_26 (Js.Num.mk (14) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_27 ← Result.ok (tmp14)
      Result.ok t_27
    else
      Result.ok t_26
  let t_30 ← if a.val > 14 then
      let tmp15 ← Js.add t_28 (Js.Num.mk (15) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_29 ← Result.ok (tmp15)
      Result.ok t_29
    else
      Result.ok t_28
  let t_32 ← if a.val > 15 then
      let tmp16 ← Js.add t_30 (Js.Num.mk (16) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_31 ← Result.ok (tmp16)
      Result.ok t_31
    else
      Result.ok t_30
  let t_34 ← if a.val > 16 then
      let tmp17 ← Js.add t_32 (Js.Num.mk (17) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_33 ← Result.ok (tmp17)
      Result.ok t_33
    else
      Result.ok t_32
  let t_36 ← if a.val > 17 then
      let tmp18 ← Js.add t_34 (Js.Num.mk (18) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_35 ← Result.ok (tmp18)
      Result.ok t_35
    else
      Result.ok t_34
  let t_38 ← if a.val > 18 then
      let tmp19 ← Js.add t_36 (Js.Num.mk (19) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_37 ← Result.ok (tmp19)
      Result.ok t_37
    else
      Result.ok t_36
  let t_40 ← if a.val > 19 then
      let tmp20 ← Js.add t_38 (Js.Num.mk (20) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_39 ← Result.ok (tmp20)
      Result.ok t_39
    else
      Result.ok t_38
  let t_42 ← if a.val > 20 then
      let tmp21 ← Js.add t_40 (Js.Num.mk (21) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_41 ← Result.ok (tmp21)
      Result.ok t_41
    else
      Result.ok t_40
  let t_44 ← if a.val > 21 then
      let tmp22 ← Js.add t_42 (Js.Num.mk (22) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_43 ← Result.ok (tmp22)
      Result.ok t_43
    else
      Result.ok t_42
  let t_46 ← if a.val > 22 then
      let tmp23 ← Js.add t_44 (Js.Num.mk (23) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_45 ← Result.ok (tmp23)
      Result.ok t_45
    else
      Result.ok t_44
  let t_48 ← if a.val > 23 then
      let tmp24 ← Js.add t_46 (Js.Num.mk (24) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_47 ← Result.ok (tmp24)
      Result.ok t_47
    else
      Result.ok t_46
  let t_50 ← if a.val > 24 then
      let tmp25 ← Js.add t_48 (Js.Num.mk (25) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_49 ← Result.ok (tmp25)
      Result.ok t_49
    else
      Result.ok t_48
  let t_52 ← if a.val > 25 then
      let tmp26 ← Js.add t_50 (Js.Num.mk (26) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_51 ← Result.ok (tmp26)
      Result.ok t_51
    else
      Result.ok t_50
  let t_54 ← if a.val > 26 then
      let tmp27 ← Js.add t_52 (Js.Num.mk (27) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_53 ← Result.ok (tmp27)
      Result.ok t_53
    else
      Result.ok t_52
  let t_56 ← if a.val > 27 then
      let tmp28 ← Js.add t_54 (Js.Num.mk (28) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_55 ← Result.ok (tmp28)
      Result.ok t_55
    else
      Result.ok t_54
  let t_58 ← if a.val > 28 then
      let tmp29 ← Js.add t_56 (Js.Num.mk (29) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_57 ← Result.ok (tmp29)
      Result.ok t_57
    else
      Result.ok t_56
  let t_60 ← if a.val > 29 then
      let tmp30 ← Js.add t_58 (Js.Num.mk (30) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_59 ← Result.ok (tmp30)
      Result.ok t_59
    else
      Result.ok t_58
  let t_62 ← if a.val > 30 then
      let tmp31 ← Js.add t_60 (Js.Num.mk (31) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_61 ← Result.ok (tmp31)
      Result.ok t_61
    else
      Result.ok t_60
  let t_64 ← if a.val > 31 then
      let tmp32 ← Js.add t_62 (Js.Num.mk (32) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_63 ← Result.ok (tmp32)
      Result.ok t_63
    else
      Result.ok t_62
  let t_66 ← if a.val > 32 then
      let tmp33 ← Js.add t_64 (Js.Num.mk (33) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_65 ← Result.ok (tmp33)
      Result.ok t_65
    else
      Result.ok t_64
  let t_68 ← if a.val > 33 then
      let tmp34 ← Js.add t_66 (Js.Num.mk (34) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_67 ← Result.ok (tmp34)
      Result.ok t_67
    else
      Result.ok t_66
  let t_70 ← if a.val > 34 then
      let tmp35 ← Js.add t_68 (Js.Num.mk (35) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_69 ← Result.ok (tmp35)
      Result.ok t_69
    else
      Result.ok t_68
  let t_72 ← if a.val > 35 then
      let tmp36 ← Js.add t_70 (Js.Num.mk (36) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_71 ← Result.ok (tmp36)
      Result.ok t_71
    else
      Result.ok t_70
  let t_74 ← if a.val > 36 then
      let tmp37 ← Js.add t_72 (Js.Num.mk (37) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_73 ← Result.ok (tmp37)
      Result.ok t_73
    else
      Result.ok t_72
  let t_76 ← if a.val > 37 then
      let tmp38 ← Js.add t_74 (Js.Num.mk (38) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_75 ← Result.ok (tmp38)
      Result.ok t_75
    else
      Result.ok t_74
  let t_78 ← if a.val > 38 then
      let tmp39 ← Js.add t_76 (Js.Num.mk (39) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_77 ← Result.ok (tmp39)
      Result.ok t_77
    else
      Result.ok t_76
  let t_80 ← if a.val > 39 then
      let tmp40 ← Js.add t_78 (Js.Num.mk (40) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_79 ← Result.ok (tmp40)
      Result.ok t_79
    else
      Result.ok t_78
  let t_82 ← if a.val > 40 then
      let tmp41 ← Js.add t_80 (Js.Num.mk (41) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_81 ← Result.ok (tmp41)
      Result.ok t_81
    else
      Result.ok t_80
  let t_84 ← if a.val > 41 then
      let tmp42 ← Js.add t_82 (Js.Num.mk (42) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_83 ← Result.ok (tmp42)
      Result.ok t_83
    else
      Result.ok t_82
  let t_86 ← if a.val > 42 then
      let tmp43 ← Js.add t_84 (Js.Num.mk (43) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_85 ← Result.ok (tmp43)
      Result.ok t_85
    else
      Result.ok t_84
  let t_88 ← if a.val > 43 then
      let tmp44 ← Js.add t_86 (Js.Num.mk (44) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_87 ← Result.ok (tmp44)
      Result.ok t_87
    else
      Result.ok t_86
  let t_90 ← if a.val > 44 then
      let tmp45 ← Js.add t_88 (Js.Num.mk (45) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_89 ← Result.ok (tmp45)
      Result.ok t_89
    else
      Result.ok t_88
  let t_92 ← if a.val > 45 then
      let tmp46 ← Js.add t_90 (Js.Num.mk (46) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_91 ← Result.ok (tmp46)
      Result.ok t_91
    else
      Result.ok t_90
  let t_94 ← if a.val > 46 then
      let tmp47 ← Js.add t_92 (Js.Num.mk (47) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_93 ← Result.ok (tmp47)
      Result.ok t_93
    else
      Result.ok t_92
  let t_96 ← if a.val > 47 then
      let tmp48 ← Js.add t_94 (Js.Num.mk (48) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_95 ← Result.ok (tmp48)
      Result.ok t_95
    else
      Result.ok t_94
  let t_98 ← if a.val > 48 then
      let tmp49 ← Js.add t_96 (Js.Num.mk (49) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_97 ← Result.ok (tmp49)
      Result.ok t_97
    else
      Result.ok t_96
  let t_100 ← if a.val > 49 then
      let tmp50 ← Js.add t_98 (Js.Num.mk (50) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_99 ← Result.ok (tmp50)
      Result.ok t_99
    else
      Result.ok t_98
  let t_102 ← if a.val > 50 then
      let tmp51 ← Js.add t_100 (Js.Num.mk (51) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_101 ← Result.ok (tmp51)
      Result.ok t_101
    else
      Result.ok t_100
  let t_104 ← if a.val > 51 then
      let tmp52 ← Js.add t_102 (Js.Num.mk (52) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_103 ← Result.ok (tmp52)
      Result.ok t_103
    else
      Result.ok t_102
  let t_106 ← if a.val > 52 then
      let tmp53 ← Js.add t_104 (Js.Num.mk (53) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_105 ← Result.ok (tmp53)
      Result.ok t_105
    else
      Result.ok t_104
  let t_108 ← if a.val > 53 then
      let tmp54 ← Js.add t_106 (Js.Num.mk (54) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_107 ← Result.ok (tmp54)
      Result.ok t_107
    else
      Result.ok t_106
  let t_110 ← if a.val > 54 then
      let tmp55 ← Js.add t_108 (Js.Num.mk (55) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_109 ← Result.ok (tmp55)
      Result.ok t_109
    else
      Result.ok t_108
  let t_112 ← if a.val > 55 then
      let tmp56 ← Js.add t_110 (Js.Num.mk (56) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_111 ← Result.ok (tmp56)
      Result.ok t_111
    else
      Result.ok t_110
  let t_114 ← if a.val > 56 then
      let tmp57 ← Js.add t_112 (Js.Num.mk (57) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_113 ← Result.ok (tmp57)
      Result.ok t_113
    else
      Result.ok t_112
  let t_116 ← if a.val > 57 then
      let tmp58 ← Js.add t_114 (Js.Num.mk (58) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_115 ← Result.ok (tmp58)
      Result.ok t_115
    else
      Result.ok t_114
  let t_118 ← if a.val > 58 then
      let tmp59 ← Js.add t_116 (Js.Num.mk (59) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_117 ← Result.ok (tmp59)
      Result.ok t_117
    else
      Result.ok t_116
  let t_120 ← if a.val > 59 then
      let tmp60 ← Js.add t_118 (Js.Num.mk (60) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_119 ← Result.ok (tmp60)
      Result.ok t_119
    else
      Result.ok t_118
  let t_122 ← if a.val > 60 then
      let tmp61 ← Js.add t_120 (Js.Num.mk (61) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_121 ← Result.ok (tmp61)
      Result.ok t_121
    else
      Result.ok t_120
  let t_124 ← if a.val > 61 then
      let tmp62 ← Js.add t_122 (Js.Num.mk (62) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_123 ← Result.ok (tmp62)
      Result.ok t_123
    else
      Result.ok t_122
  let t_126 ← if a.val > 62 then
      let tmp63 ← Js.add t_124 (Js.Num.mk (63) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_125 ← Result.ok (tmp63)
      Result.ok t_125
    else
      Result.ok t_124
  let t_128 ← if a.val > 63 then
      let tmp64 ← Js.add t_126 (Js.Num.mk (64) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_127 ← Result.ok (tmp64)
      Result.ok t_127
    else
      Result.ok t_126
  let t_130 ← if a.val > 64 then
      let tmp65 ← Js.add t_128 (Js.Num.mk (65) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_129 ← Result.ok (tmp65)
      Result.ok t_129
    else
      Result.ok t_128
  let t_132 ← if a.val > 65 then
      let tmp66 ← Js.add t_130 (Js.Num.mk (66) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_131 ← Result.ok (tmp66)
      Result.ok t_131
    else
      Result.ok t_130
  let t_134 ← if a.val > 66 then
      let tmp67 ← Js.add t_132 (Js.Num.mk (67) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_133 ← Result.ok (tmp67)
      Result.ok t_133
    else
      Result.ok t_132
  let t_136 ← if a.val > 67 then
      let tmp68 ← Js.add t_134 (Js.Num.mk (68) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_135 ← Result.ok (tmp68)
      Result.ok t_135
    else
      Result.ok t_134
  let t_138 ← if a.val > 68 then
      let tmp69 ← Js.add t_136 (Js.Num.mk (69) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_137 ← Result.ok (tmp69)
      Result.ok t_137
    else
      Result.ok t_136
  let t_140 ← if a.val > 69 then
      let tmp70 ← Js.add t_138 (Js.Num.mk (70) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_139 ← Result.ok (tmp70)
      Result.ok t_139
    else
      Result.ok t_138
  let t_142 ← if a.val > 70 then
      let tmp71 ← Js.add t_140 (Js.Num.mk (71) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_141 ← Result.ok (tmp71)
      Result.ok t_141
    else
      Result.ok t_140
  let t_144 ← if a.val > 71 then
      let tmp72 ← Js.add t_142 (Js.Num.mk (72) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_143 ← Result.ok (tmp72)
      Result.ok t_143
    else
      Result.ok t_142
  let t_146 ← if a.val > 72 then
      let tmp73 ← Js.add t_144 (Js.Num.mk (73) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_145 ← Result.ok (tmp73)
      Result.ok t_145
    else
      Result.ok t_144
  let t_148 ← if a.val > 73 then
      let tmp74 ← Js.add t_146 (Js.Num.mk (74) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_147 ← Result.ok (tmp74)
      Result.ok t_147
    else
      Result.ok t_146
  let t_150 ← if a.val > 74 then
      let tmp75 ← Js.add t_148 (Js.Num.mk (75) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_149 ← Result.ok (tmp75)
      Result.ok t_149
    else
      Result.ok t_148
  let t_152 ← if a.val > 75 then
      let tmp76 ← Js.add t_150 (Js.Num.mk (76) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_151 ← Result.ok (tmp76)
      Result.ok t_151
    else
      Result.ok t_150
  let t_154 ← if a.val > 76 then
      let tmp77 ← Js.add t_152 (Js.Num.mk (77) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_153 ← Result.ok (tmp77)
      Result.ok t_153
    else
      Result.ok t_152
  let t_156 ← if a.val > 77 then
      let tmp78 ← Js.add t_154 (Js.Num.mk (78) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_155 ← Result.ok (tmp78)
      Result.ok t_155
    else
      Result.ok t_154
  let t_158 ← if a.val > 78 then
      let tmp79 ← Js.add t_156 (Js.Num.mk (79) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_157 ← Result.ok (tmp79)
      Result.ok t_157
    else
      Result.ok t_156
  let t_160 ← if a.val > 79 then
      let tmp80 ← Js.add t_158 (Js.Num.mk (80) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_159 ← Result.ok (tmp80)
      Result.ok t_159
    else
      Result.ok t_158
  let t_162 ← if a.val > 80 then
      let tmp81 ← Js.add t_160 (Js.Num.mk (81) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_161 ← Result.ok (tmp81)
      Result.ok t_161
    else
      Result.ok t_160
  let t_164 ← if a.val > 81 then
      let tmp82 ← Js.add t_162 (Js.Num.mk (82) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_163 ← Result.ok (tmp82)
      Result.ok t_163
    else
      Result.ok t_162
  let t_166 ← if a.val > 82 then
      let tmp83 ← Js.add t_164 (Js.Num.mk (83) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_165 ← Result.ok (tmp83)
      Result.ok t_165
    else
      Result.ok t_164
  let t_168 ← if a.val > 83 then
      let tmp84 ← Js.add t_166 (Js.Num.mk (84) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_167 ← Result.ok (tmp84)
      Result.ok t_167
    else
      Result.ok t_166
  let t_170 ← if a.val > 84 then
      let tmp85 ← Js.add t_168 (Js.Num.mk (85) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_169 ← Result.ok (tmp85)
      Result.ok t_169
    else
      Result.ok t_168
  let t_172 ← if a.val > 85 then
      let tmp86 ← Js.add t_170 (Js.Num.mk (86) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_171 ← Result.ok (tmp86)
      Result.ok t_171
    else
      Result.ok t_170
  let t_174 ← if a.val > 86 then
      let tmp87 ← Js.add t_172 (Js.Num.mk (87) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_173 ← Result.ok (tmp87)
      Result.ok t_173
    else
      Result.ok t_172
  let t_176 ← if a.val > 87 then
      let tmp88 ← Js.add t_174 (Js.Num.mk (88) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_175 ← Result.ok (tmp88)
      Result.ok t_175
    else
      Result.ok t_174
  let t_178 ← if a.val > 88 then
      let tmp89 ← Js.add t_176 (Js.Num.mk (89) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_177 ← Result.ok (tmp89)
      Result.ok t_177
    else
      Result.ok t_176
  let t_180 ← if a.val > 89 then
      let tmp90 ← Js.add t_178 (Js.Num.mk (90) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_179 ← Result.ok (tmp90)
      Result.ok t_179
    else
      Result.ok t_178
  let t_182 ← if a.val > 90 then
      let tmp91 ← Js.add t_180 (Js.Num.mk (91) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_181 ← Result.ok (tmp91)
      Result.ok t_181
    else
      Result.ok t_180
  let t_184 ← if a.val > 91 then
      let tmp92 ← Js.add t_182 (Js.Num.mk (92) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_183 ← Result.ok (tmp92)
      Result.ok t_183
    else
      Result.ok t_182
  let t_186 ← if a.val > 92 then
      let tmp93 ← Js.add t_184 (Js.Num.mk (93) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_185 ← Result.ok (tmp93)
      Result.ok t_185
    else
      Result.ok t_184
  let t_188 ← if a.val > 93 then
      let tmp94 ← Js.add t_186 (Js.Num.mk (94) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_187 ← Result.ok (tmp94)
      Result.ok t_187
    else
      Result.ok t_186
  let t_190 ← if a.val > 94 then
      let tmp95 ← Js.add t_188 (Js.Num.mk (95) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_189 ← Result.ok (tmp95)
      Result.ok t_189
    else
      Result.ok t_188
  let t_192 ← if a.val > 95 then
      let tmp96 ← Js.add t_190 (Js.Num.mk (96) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_191 ← Result.ok (tmp96)
      Result.ok t_191
    else
      Result.ok t_190
  let t_194 ← if a.val > 96 then
      let tmp97 ← Js.add t_192 (Js.Num.mk (97) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_193 ← Result.ok (tmp97)
      Result.ok t_193
    else
      Result.ok t_192
  let t_196 ← if a.val > 97 then
      let tmp98 ← Js.add t_194 (Js.Num.mk (98) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_195 ← Result.ok (tmp98)
      Result.ok t_195
    else
      Result.ok t_194
  let t_198 ← if a.val > 98 then
      let tmp99 ← Js.add t_196 (Js.Num.mk (99) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_197 ← Result.ok (tmp99)
      Result.ok t_197
    else
      Result.ok t_196
  let t_200 ← if a.val > 99 then
      let tmp100 ← Js.add t_198 (Js.Num.mk (100) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_199 ← Result.ok (tmp100)
      Result.ok t_199
    else
      Result.ok t_198
  let t_202 ← if a.val > 100 then
      let tmp101 ← Js.add t_200 (Js.Num.mk (101) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_201 ← Result.ok (tmp101)
      Result.ok t_201
    else
      Result.ok t_200
  let t_204 ← if a.val > 101 then
      let tmp102 ← Js.add t_202 (Js.Num.mk (102) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_203 ← Result.ok (tmp102)
      Result.ok t_203
    else
      Result.ok t_202
  let t_206 ← if a.val > 102 then
      let tmp103 ← Js.add t_204 (Js.Num.mk (103) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_205 ← Result.ok (tmp103)
      Result.ok t_205
    else
      Result.ok t_204
  let t_208 ← if a.val > 103 then
      let tmp104 ← Js.add t_206 (Js.Num.mk (104) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_207 ← Result.ok (tmp104)
      Result.ok t_207
    else
      Result.ok t_206
  let t_210 ← if a.val > 104 then
      let tmp105 ← Js.add t_208 (Js.Num.mk (105) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_209 ← Result.ok (tmp105)
      Result.ok t_209
    else
      Result.ok t_208
  let t_212 ← if a.val > 105 then
      let tmp106 ← Js.add t_210 (Js.Num.mk (106) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_211 ← Result.ok (tmp106)
      Result.ok t_211
    else
      Result.ok t_210
  let t_214 ← if a.val > 106 then
      let tmp107 ← Js.add t_212 (Js.Num.mk (107) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_213 ← Result.ok (tmp107)
      Result.ok t_213
    else
      Result.ok t_212
  let t_216 ← if a.val > 107 then
      let tmp108 ← Js.add t_214 (Js.Num.mk (108) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_215 ← Result.ok (tmp108)
      Result.ok t_215
    else
      Result.ok t_214
  let t_218 ← if a.val > 108 then
      let tmp109 ← Js.add t_216 (Js.Num.mk (109) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_217 ← Result.ok (tmp109)
      Result.ok t_217
    else
      Result.ok t_216
  let t_220 ← if a.val > 109 then
      let tmp110 ← Js.add t_218 (Js.Num.mk (110) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_219 ← Result.ok (tmp110)
      Result.ok t_219
    else
      Result.ok t_218
  let t_222 ← if a.val > 110 then
      let tmp111 ← Js.add t_220 (Js.Num.mk (111) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_221 ← Result.ok (tmp111)
      Result.ok t_221
    else
      Result.ok t_220
  let t_224 ← if a.val > 111 then
      let tmp112 ← Js.add t_222 (Js.Num.mk (112) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_223 ← Result.ok (tmp112)
      Result.ok t_223
    else
      Result.ok t_222
  let t_226 ← if a.val > 112 then
      let tmp113 ← Js.add t_224 (Js.Num.mk (113) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_225 ← Result.ok (tmp113)
      Result.ok t_225
    else
      Result.ok t_224
  let t_228 ← if a.val > 113 then
      let tmp114 ← Js.add t_226 (Js.Num.mk (114) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_227 ← Result.ok (tmp114)
      Result.ok t_227
    else
      Result.ok t_226
  let t_230 ← if a.val > 114 then
      let tmp115 ← Js.add t_228 (Js.Num.mk (115) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_229 ← Result.ok (tmp115)
      Result.ok t_229
    else
      Result.ok t_228
  let t_232 ← if a.val > 115 then
      let tmp116 ← Js.add t_230 (Js.Num.mk (116) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_231 ← Result.ok (tmp116)
      Result.ok t_231
    else
      Result.ok t_230
  let t_234 ← if a.val > 116 then
      let tmp117 ← Js.add t_232 (Js.Num.mk (117) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_233 ← Result.ok (tmp117)
      Result.ok t_233
    else
      Result.ok t_232
  let t_236 ← if a.val > 117 then
      let tmp118 ← Js.add t_234 (Js.Num.mk (118) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_235 ← Result.ok (tmp118)
      Result.ok t_235
    else
      Result.ok t_234
  let t_238 ← if a.val > 118 then
      let tmp119 ← Js.add t_236 (Js.Num.mk (119) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_237 ← Result.ok (tmp119)
      Result.ok t_237
    else
      Result.ok t_236
  let t_240 ← if a.val > 119 then
      let tmp120 ← Js.add t_238 (Js.Num.mk (120) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_239 ← Result.ok (tmp120)
      Result.ok t_239
    else
      Result.ok t_238
  let t_242 ← if a.val > 120 then
      let tmp121 ← Js.add t_240 (Js.Num.mk (121) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_241 ← Result.ok (tmp121)
      Result.ok t_241
    else
      Result.ok t_240
  let t_244 ← if a.val > 121 then
      let tmp122 ← Js.add t_242 (Js.Num.mk (122) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_243 ← Result.ok (tmp122)
      Result.ok t_243
    else
      Result.ok t_242
  let t_246 ← if a.val > 122 then
      let tmp123 ← Js.add t_244 (Js.Num.mk (123) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_245 ← Result.ok (tmp123)
      Result.ok t_245
    else
      Result.ok t_244
  let t_248 ← if a.val > 123 then
      let tmp124 ← Js.add t_246 (Js.Num.mk (124) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_247 ← Result.ok (tmp124)
      Result.ok t_247
    else
      Result.ok t_246
  let t_250 ← if a.val > 124 then
      let tmp125 ← Js.add t_248 (Js.Num.mk (125) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_249 ← Result.ok (tmp125)
      Result.ok t_249
    else
      Result.ok t_248
  let t_252 ← if a.val > 125 then
      let tmp126 ← Js.add t_250 (Js.Num.mk (126) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_251 ← Result.ok (tmp126)
      Result.ok t_251
    else
      Result.ok t_250
  let t_254 ← if a.val > 126 then
      let tmp127 ← Js.add t_252 (Js.Num.mk (127) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_253 ← Result.ok (tmp127)
      Result.ok t_253
    else
      Result.ok t_252
  let t_256 ← if a.val > 127 then
      let tmp128 ← Js.add t_254 (Js.Num.mk (128) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_255 ← Result.ok (tmp128)
      Result.ok t_255
    else
      Result.ok t_254
  let t_258 ← if a.val > 128 then
      let tmp129 ← Js.add t_256 (Js.Num.mk (129) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_257 ← Result.ok (tmp129)
      Result.ok t_257
    else
      Result.ok t_256
  let t_260 ← if a.val > 129 then
      let tmp130 ← Js.add t_258 (Js.Num.mk (130) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_259 ← Result.ok (tmp130)
      Result.ok t_259
    else
      Result.ok t_258
  let t_262 ← if a.val > 130 then
      let tmp131 ← Js.add t_260 (Js.Num.mk (131) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_261 ← Result.ok (tmp131)
      Result.ok t_261
    else
      Result.ok t_260
  let t_264 ← if a.val > 131 then
      let tmp132 ← Js.add t_262 (Js.Num.mk (132) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_263 ← Result.ok (tmp132)
      Result.ok t_263
    else
      Result.ok t_262
  let t_266 ← if a.val > 132 then
      let tmp133 ← Js.add t_264 (Js.Num.mk (133) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_265 ← Result.ok (tmp133)
      Result.ok t_265
    else
      Result.ok t_264
  let t_268 ← if a.val > 133 then
      let tmp134 ← Js.add t_266 (Js.Num.mk (134) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_267 ← Result.ok (tmp134)
      Result.ok t_267
    else
      Result.ok t_266
  let t_270 ← if a.val > 134 then
      let tmp135 ← Js.add t_268 (Js.Num.mk (135) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_269 ← Result.ok (tmp135)
      Result.ok t_269
    else
      Result.ok t_268
  let t_272 ← if a.val > 135 then
      let tmp136 ← Js.add t_270 (Js.Num.mk (136) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_271 ← Result.ok (tmp136)
      Result.ok t_271
    else
      Result.ok t_270
  let t_274 ← if a.val > 136 then
      let tmp137 ← Js.add t_272 (Js.Num.mk (137) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_273 ← Result.ok (tmp137)
      Result.ok t_273
    else
      Result.ok t_272
  let t_276 ← if a.val > 137 then
      let tmp138 ← Js.add t_274 (Js.Num.mk (138) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_275 ← Result.ok (tmp138)
      Result.ok t_275
    else
      Result.ok t_274
  let t_278 ← if a.val > 138 then
      let tmp139 ← Js.add t_276 (Js.Num.mk (139) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_277 ← Result.ok (tmp139)
      Result.ok t_277
    else
      Result.ok t_276
  let t_280 ← if a.val > 139 then
      let tmp140 ← Js.add t_278 (Js.Num.mk (140) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_279 ← Result.ok (tmp140)
      Result.ok t_279
    else
      Result.ok t_278
  let t_282 ← if a.val > 140 then
      let tmp141 ← Js.add t_280 (Js.Num.mk (141) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_281 ← Result.ok (tmp141)
      Result.ok t_281
    else
      Result.ok t_280
  let t_284 ← if a.val > 141 then
      let tmp142 ← Js.add t_282 (Js.Num.mk (142) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_283 ← Result.ok (tmp142)
      Result.ok t_283
    else
      Result.ok t_282
  let t_286 ← if a.val > 142 then
      let tmp143 ← Js.add t_284 (Js.Num.mk (143) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_285 ← Result.ok (tmp143)
      Result.ok t_285
    else
      Result.ok t_284
  let t_288 ← if a.val > 143 then
      let tmp144 ← Js.add t_286 (Js.Num.mk (144) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_287 ← Result.ok (tmp144)
      Result.ok t_287
    else
      Result.ok t_286
  let t_290 ← if a.val > 144 then
      let tmp145 ← Js.add t_288 (Js.Num.mk (145) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_289 ← Result.ok (tmp145)
      Result.ok t_289
    else
      Result.ok t_288
  let t_292 ← if a.val > 145 then
      let tmp146 ← Js.add t_290 (Js.Num.mk (146) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_291 ← Result.ok (tmp146)
      Result.ok t_291
    else
      Result.ok t_290
  let t_294 ← if a.val > 146 then
      let tmp147 ← Js.add t_292 (Js.Num.mk (147) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_293 ← Result.ok (tmp147)
      Result.ok t_293
    else
      Result.ok t_292
  let t_296 ← if a.val > 147 then
      let tmp148 ← Js.add t_294 (Js.Num.mk (148) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_295 ← Result.ok (tmp148)
      Result.ok t_295
    else
      Result.ok t_294
  let t_298 ← if a.val > 148 then
      let tmp149 ← Js.add t_296 (Js.Num.mk (149) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_297 ← Result.ok (tmp149)
      Result.ok t_297
    else
      Result.ok t_296
  let t_300 ← if a.val > 149 then
      let tmp150 ← Js.add t_298 (Js.Num.mk (150) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_299 ← Result.ok (tmp150)
      Result.ok t_299
    else
      Result.ok t_298
  let t_302 ← if a.val > 150 then
      let tmp151 ← Js.add t_300 (Js.Num.mk (151) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_301 ← Result.ok (tmp151)
      Result.ok t_301
    else
      Result.ok t_300
  let t_304 ← if a.val > 151 then
      let tmp152 ← Js.add t_302 (Js.Num.mk (152) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_303 ← Result.ok (tmp152)
      Result.ok t_303
    else
      Result.ok t_302
  let t_306 ← if a.val > 152 then
      let tmp153 ← Js.add t_304 (Js.Num.mk (153) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_305 ← Result.ok (tmp153)
      Result.ok t_305
    else
      Result.ok t_304
  let t_308 ← if a.val > 153 then
      let tmp154 ← Js.add t_306 (Js.Num.mk (154) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_307 ← Result.ok (tmp154)
      Result.ok t_307
    else
      Result.ok t_306
  let t_310 ← if a.val > 154 then
      let tmp155 ← Js.add t_308 (Js.Num.mk (155) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_309 ← Result.ok (tmp155)
      Result.ok t_309
    else
      Result.ok t_308
  let t_312 ← if a.val > 155 then
      let tmp156 ← Js.add t_310 (Js.Num.mk (156) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_311 ← Result.ok (tmp156)
      Result.ok t_311
    else
      Result.ok t_310
  let t_314 ← if a.val > 156 then
      let tmp157 ← Js.add t_312 (Js.Num.mk (157) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_313 ← Result.ok (tmp157)
      Result.ok t_313
    else
      Result.ok t_312
  let t_316 ← if a.val > 157 then
      let tmp158 ← Js.add t_314 (Js.Num.mk (158) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_315 ← Result.ok (tmp158)
      Result.ok t_315
    else
      Result.ok t_314
  let t_318 ← if a.val > 158 then
      let tmp159 ← Js.add t_316 (Js.Num.mk (159) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_317 ← Result.ok (tmp159)
      Result.ok t_317
    else
      Result.ok t_316
  let t_320 ← if a.val > 159 then
      let tmp160 ← Js.add t_318 (Js.Num.mk (160) (of_decide_eq_true rfl) (of_decide_eq_true rfl))
      let t_319 ← Result.ok (tmp160)
      Result.ok t_319
    else
      Result.ok t_318
  Result.ok t_320

