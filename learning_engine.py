import os
import sys
import math
import time
from _weakrefset import WeakSet

MAX_CALCULATE = 250000000
HardCode = {}
Relation = []
NewFault = []
LengthCount = {}
Process = []
Finding = []
Paths = []
Matrix = []
current_time = time.time()
time_out = 0

class PathInformation:
    def __init__(self, tcse, cks):
        self.cksum = cks
        self.testcases = [tcse] if tcse else []
        self.nums = 1 if tcse else 0
        self.totalExec = 1 if tcse else 0
        self.minLength = len(tcse) if tcse else 0
        self.maxLength = len(tcse) if tcse else 0
        self.fixedLength = -1
        self.relation = []
        self.fault = 0
        self.reg = []
        self.pos = []
        self.useModel = 0
        self.isSeed = 0
        self.diff = 0

    def update(self, node):
        self.testcases.append(node['Testcase'])
        self.nums += 1
        self.totalExec += 1
        tempLength = len(node['Testcase'])
        self.minLength = min(self.minLength, tempLength)
        self.maxLength = max(self.maxLength, tempLength)
        if node['Fault case'] != '0':
            self.fault = int(node['Fault case'])

    def delete(self, node):
        self.testcases.remove(node['Testcase'])
        self.nums -= 1
        self.totalExec -= 1
        if self.nums == 0:
            self.minLength = 0
        else:
            self.minLength = min(len(tc) for tc in self.testcases)

    def add_node(self, node):
        if node['Cksum'] != self.cksum:
            return 0
        else:
            self.update(node)

    def analysis_feature(self):
        if self.maxLength == self.minLength:
            self.fixedLength = self.maxLength
        else:
            self.fixedLength = -1

        if self.nums == 0:
            return 0

        tempReg, tempPos = get_format(self.testcases[:min(self.nums, MAX_CALCULATE // (self.maxLength * self.maxLength))])
        if self.reg:
            self.reg, self.pos = generate_new_reg_from_two_regs(self.reg, self.pos, tempReg, tempPos)
            self.useModel = 1 if self.reg != self.reg or self.pos != self.pos else 2
        else:
            self.useModel = 1
            self.reg = tempReg
            self.pos = tempPos

        if not self.reg:
            self.useModel = 0


def get_hardcode(testcases):
    minLength = min(len(tc) for tc in testcases)
    tempHardcode = [tc[i] if all(tcse[i] == tc[i] for tcse in testcases) else '' for i in range(minLength)]
    hardcode = {}
    i = 0
    while i < len(tempHardcode):
        if tempHardcode[i] != '':
            j = i
            while i < len(tempHardcode) and tempHardcode[i] != '':
                i += 1
            hardcode[j] = ''.join(tempHardcode[j:i])
        i += 1
    return hardcode

def splice_testcases(testcases, hardcode):
    order1 = sorted(hardcode.keys())
    order2 = [i + len(hardcode[i]) for i in order1]
    if 0 not in order1:
        order2.insert(0, 0)
    else:
        order1.pop(0)

    splice = [[tc[order2[i]:order1[i]] for i in range(len(order1))] + [tc[order2[-1]:]] for tc in testcases]
    result = [[splice[j][i] for j in range(len(splice))] for i in range(len(splice[0]))]
    return result

def get_format(testcases):
    if not testcases:
        return [], []
    hardcode = get_hardcode(testcases)
    reg, pos = get_regular(testcases, hardcode)
    return reg, pos

def get_dictionary(strings):
    dic = list(set(strings[0]).intersection(*strings))
    return dic

def get_subString(s1, s2, dic):
    subString = []
    i = 0
    while i < len(s1):
        flag = False
        j = 0
        maxString = ''
        while j < len(s2):
            tempString = ''
            k = 0
            while i + k < len(s1) and j + k < len(s2) and s1[i + k] == s2[j + k] and s1[i + k] in dic:
                flag = True
                tempString += s1[i + k]
                k += 1
            if k > len(maxString):
                maxString = tempString
            if k == 0:
                j += 1
            else:
                j += k
        if not flag:
            i += 1
        else:
            subString.append(maxString)
            i += len(maxString)
    return subString

def find_min_string(strings):
    min_sub = min(strings, key=lambda s: sum(len(sub) for sub in s))
    return min_sub

def get_position(testcases, minString):
    regular = minString
    lengthOfLast = len(regular[-1])
    end = all(tscs[-lengthOfLast:] == regular[-1] for tscs in testcases)
    position = [-2] * len(regular)
    if not end:
        position[-1] = -1
    return regular, position

def generate_regular(testcases, time_limit):
    dictionary = get_dictionary(testcases)
    if not dictionary:
        return [], []
    subString = []
    num = len(testcases)
    for i in range(num):
        if time.time() - current_time > time_limit:
            time_out = 1
            num = i
            break
        subString.append(get_subString(testcases[i], testcases[(i + 1) % len(testcases)], dictionary))
    minString = find_min_string(subString)
    if minString:
        minString = [sub for sub in minString if all(sub in tc for tc in testcases[:num])]
    if minString:
        reg, pos = get_position(testcases[:num], minString)
        for tc in testcases[:num]:
            i, j = 0, 0
            while i < len(reg):
                if pos[i] == -2:
                    if reg[i] in tc[j:]:
                        j = j + tc[j:].index(reg[i]) + len(reg[i])
                        i += 1
                    else:
                        reg.pop(i)
                        pos.pop(i)
                elif pos[i] == -1 and tc[-len(reg[i]):] != reg[i]:
                    reg.pop(i)
                    pos.pop(i)
                else:
                    j = pos[i] + len(reg[i])
                    i += 1
    return reg, pos

def get_regular(testcases, hardcode):
    splice = splice_testcases(testcases, hardcode)
    time_limit = 15.0 / len(splice) if splice else 15.0
    tempReg, tempPos = zip(*(generate_regular(s, time_limit) for s in splice))
    reg, pos = [], []
    if 0 in hardcode:
        for i in range(len(tempReg)):
            reg.append(hardcode[sorted(hardcode.keys())[i]])
            pos.append(sorted(hardcode.keys())[i])
            reg.extend(tempReg[i])
            pos.extend(tempPos[i])
    else:
        for i in range(len(tempReg) - 1):
            reg.extend(tempReg[i])
            pos.extend(tempPos[i])
            reg.append(hardcode[sorted(hardcode.keys())[i]])
            pos.append(sorted(hardcode.keys())[i])
        reg.extend(tempReg[-1])
        pos.extend(tempPos[-1])
    return reg, pos

def get_public_hardcode(reg1, pos1, reg2, pos2):
    hardcode1 = {pos1[i] + j: reg1[i][j] for i in range(len(pos1)) if pos1[i] not in [-2, -1] for j in range(len(reg1[i]))}
    hardcode2 = {pos2[i] + j: reg2[i][j] for i in range(len(pos2)) if pos2[i] not in [-2, -1] for j in range(len(reg2[i]))}
    if not hardcode1 or not hardcode2:
        return {}
    tempHardcode = ['' if i not in hardcode1 or hardcode1[i] != hardcode2[i] else hardcode1[i] for i in range(max(max(hardcode1.keys()), max(hardcode2.keys())) + 1)]
    hardcode = {}
    i = 0
    while i < len(tempHardcode):
        if tempHardcode[i] != '':
            j = i
            while i < len(tempHardcode) and tempHardcode[i] != '':
                i += 1
            hardcode[j] = ''.join(tempHardcode[j:i])
        i += 1
    return hardcode

def generate_new_reg_from_two_regs(reg1, pos1, reg2, pos2):
    hardcode = get_public_hardcode(reg1, pos1, reg2, pos2)
    testcases = [''.join([reg1[i] for i in range(len(reg1)) if pos1[i] != -2])] * 2
    splice = splice_testcases(testcases, hardcode)
    time_limit = 15.0 / len(splice) if splice else 15.0
    tempReg, tempPos = zip(*(generate_regular(s, time_limit) for s in splice))
    reg, pos = [], []
    if 0 in hardcode:
        for i in range(len(tempReg)):
            reg.append(hardcode[sorted(hardcode.keys())[i]])
            pos.append(sorted(hardcode.keys())[i])
            reg.extend(tempReg[i])
            pos.extend(tempPos[i])
    else:
        for i in range(len(tempReg) - 1):
            reg.extend(tempReg[i])
            pos.extend(tempPos[i])
            reg.append(hardcode[sorted(hardcode.keys())[i]])
            pos.append(sorted(hardcode.keys())[i])
        reg.extend(tempReg[-1])
        pos.extend(tempPos[-1])
    return reg, pos
