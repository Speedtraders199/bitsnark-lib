
import fs from 'fs';
import groth16Verify, { Key, Proof as Step1_Proof } from './step1/verifier';
import { step1_vm } from './step1/vm/vm';
import { step2_vm } from './step2/vm/vm';
import { ProgramLine, SavedVm } from './common/saved-vm';
import { InstrCode as Step1_InstrCode } from './step1/vm/types';
import { InstrCode as Step2_InstrCode } from './step2/vm/types';
import { validateInstr } from './step2/final-step';
import { Runner as Step1_Runner } from './step1/vm/runner';
import { Runner as Step2_Runner } from './step2/vm/runner';
import { Register } from './common/register';
import { verifyStep2Instr } from './step3/verify-step2-instr';
import { Bitcoin } from './step3/bitcoin';
import { Compressor } from './taproot/compressor';

type Step1Program = SavedVm<Step1_InstrCode>;
type Step2Program = SavedVm<Step2_InstrCode>;

function step1(): Step1Program {
    const vKey = {
        "protocol": "groth16",
        "curve": "bn128",
        "nPublic": 2,
        "vk_alpha_1": [
            "21712882250472796272161788137658761599131127155430822464824672498476826388551",
            "552741532735314699926400759823293923105907069604986766042478074962192337366",
            "1"
        ],
        "vk_beta_2": [
            [
                "11454657900582179986942752433396175393379495277505314089098948702824581371073",
                "12058235453740420034921457986465505463457514607198777288482514440281218605028"
            ],
            [
                "9245012449840884679075676193884780481706956365868051138079687915934413768997",
                "14348239919612624225209599824418433914444557994830931450885824657802418934202"
            ],
            [
                "1",
                "0"
            ]
        ],
        "vk_gamma_2": [
            [
                "10857046999023057135944570762232829481370756359578518086990519993285655852781",
                "11559732032986387107991004021392285783925812861821192530917403151452391805634"
            ],
            [
                "8495653923123431417604973247489272438418190587263600148770280649306958101930",
                "4082367875863433681332203403145435568316851327593401208105741076214120093531"
            ],
            [
                "1",
                "0"
            ]
        ],
        "vk_delta_2": [
            [
                "19749955201276019113767908335412065539635760453824542580852110315987111407211",
                "15438115071310379730640950544985926952604930553405319893567683759101083548862"
            ],
            [
                "8081373083339833367863828227041427035692797663482727195083250203573955986378",
                "5039646762941336679168675399139810890393860924275729758598296551114657136302"
            ],
            [
                "1",
                "0"
            ]
        ],
        "vk_alphabeta_12": [
            [
                [
                    "83246192919196632629911293082507223331535741214291277753177009822773807039",
                    "9147681130761915124992103762624270923270578778615653504674237253332848351635"
                ],
                [
                    "14763855245243506392883735077939310098926871520831926647631912284352888124556",
                    "11103074638230520106821751403226287887956436652540939881866408662512666357442"
                ],
                [
                    "12984538483238484324045715603191758939139256752759089475975708670567228515894",
                    "8600035415405927876147079830500883365461650712915995990656852431919567914551"
                ]
            ],
            [
                [
                    "20200568705241693194370952547326466253957663538037514759379848392721636051059",
                    "7267055554614047990702204460623638378118971681095287678248229096270056718464"
                ],
                [
                    "5423010749865132785108316047507820728226882076602498556580145061887662054183",
                    "10506934983360800929453798956239960237509124064034702657335978238164078944379"
                ],
                [
                    "16912024337441250577926137093507037562957878204566913339063708506211532668467",
                    "10703864755384914750022054659634869688591627626806189011752344395366855259226"
                ]
            ]
        ],
        "IC": [
            [
                "15228319439367907688412448440498031133959967042739898244747533922285298263588",
                "7325414058263354695276256220131713148508401078319479089590352962374400955943",
                "1"
            ],
            [
                "15787697953497698366259422004335840598898242056369433499534726268976760863408",
                "13999881966261347350313268261994882673895614399911197048975752238692140366328",
                "1"
            ],
            [
                "11658042682902220805035875782281846254107538847337155467126794851474468453075",
                "17111742092987389674133413486604666043472810767103656700764313114323999544388",
                "1"
            ]
        ]
    };
    const proof = {
        "pi_a": ["4531350982720745483183896166010272188780196700199407980342269744581989148149",
            "8537072424426339037594105475681425616791387434880920465097584850313527560965",
            "1"],
        "pi_b": [
            ["2411699281801306923564935501152972918367713935498519592436730569804473762071",
                "9802075445186058683936769178514143384687031267769197843391560534835079597863"],
            ["9841644077687891842107824701324051165061919977670341286300780240127706993433",
                "542961677870429289316706958907664752199371035048761897149284127652926867503"],
            ["1", "0"]],
        "pi_c": ["3973245501156043393965035252994987222825469293526203824011347102421386558530",
            "5182492167196517803964084985226343839022108025654500361628202698319357889198",
            "1"],
        "protocol": "groth16",
        "curve": "bn128"
    };
    const publicSignals = ["19820469076730107577691234630797803937210158605698999776717232705083708883456", "11"];
    groth16Verify(Key.fromSnarkjs(vKey), Step1_Proof.fromSnarkjs(proof, publicSignals));
    if (!step1_vm.success) throw new Error('Failed.');
    step1_vm.optimizeRegs();
    return step1_vm.save();
}

function step2(compressor: Compressor, step1Program: Step1Program) {

    const step1Runner = Step1_Runner.load(step1Program);
    console.log('step 1 program size: ', step1Runner.instructions.length);

    step1Program.program.forEach((instr, step1_line) => {

        const regsBefore = step1Runner.getRegisterValues();
        step1Runner.execute(step1_line);
        const regsAfter = step1Runner.getRegisterValues();

        const a = regsBefore[instr.param1!];
        const b = regsBefore[instr.param2!];
        const c = regsAfter[instr.target!];

        step2_vm.reset();
        validateInstr(a, b, c, instr.name, instr.bit);
        if (!step2_vm.success) {
            throw new Error(`Step2 generation failed at line ${step1_line}`);
        }

        const step2_program = step2_vm.save();
        const step2Runner = Step2_Runner.load(step2_program);

        console.log('step 2 program size: ', step2Runner.instructions.length, ' instr: ', instr.name);

        step2Runner.instructions.forEach((instr, line) => {

            //console.log('step 1 line: ', step1_line, ' step 2 line: ', line);

            const regsBefore = step1Runner.getRegisterValues();
            step1Runner.execute(step1_line);
            const regsAfter = step1Runner.getRegisterValues();
            const a = regsBefore[instr.param1!];
            const b = regsBefore[instr.param2!];
            const c = regsAfter[instr.target!];

            const bitcoin = new Bitcoin();
            verifyStep2Instr(bitcoin, instr, a, b, c);
            compressor.addItem(bitcoin.programToBinary());
        });
    });
}

const compressor = new Compressor(19 + 5);
const step1_program = step1();
step2(compressor, step1_program);
